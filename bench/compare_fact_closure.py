# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Compare current fact closure with uncached and cached reference builds."""

from __future__ import annotations

import argparse
import statistics
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

WARM_SPEEDUP_MIN = 1.50
REFERENCE_OVERHEAD_MAX = 0.10
EXTRA_MEMORY_MAX = 192 * 1024


@dataclass(frozen=True)
class Scenario:
    name: str
    iterations: int


SCENARIOS = (
    Scenario("cold-chain", 512),
    Scenario("warm-chain", 6000),
    Scenario("independent", 16000),
    Scenario("collisions", 5000),
    Scenario("long-chain", 24),
    Scenario("large-batch", 1024),
    Scenario("session-reset", 14000),
    Scenario("arena-growth", 3000),
)


@dataclass(frozen=True)
class Run:
    seconds: float
    values: dict[str, int | str]


def parse_output(output: str) -> dict[str, int | str]:
    values: dict[str, int | str] = {}
    for line in output.splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        values[key] = int(value) if value.isdigit() else value
    return values


def run_once(executable: Path, scenario: Scenario, profile: bool = False) -> Run:
    command = [str(executable), scenario.name, str(scenario.iterations)]
    if profile:
        command.append("--profile-memory")
    process = subprocess.Popen(
        command,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert process.stdout is not None
    assert process.stdin is not None
    assert process.stderr is not None
    ready = process.stdout.readline().strip()
    if ready != "READY":
        process.kill()
        stderr = process.stderr.read()
        process.wait()
        raise RuntimeError(f"{executable}: expected READY, got {ready!r}: {stderr}")
    started = time.perf_counter()
    process.stdin.write("run\n")
    process.stdin.flush()
    process.stdin.close()
    output = process.stdout.read()
    stderr = process.stderr.read()
    returncode = process.wait()
    elapsed = time.perf_counter() - started
    if returncode != 0:
        raise RuntimeError(f"{executable} {scenario.name} failed with {returncode}: {stderr}")
    values = parse_output(output)
    if values.get("operations") != scenario.iterations:
        raise RuntimeError(f"{executable} {scenario.name}: malformed output")
    return Run(elapsed, values)


def median_trials(
    executables: dict[str, Path], scenario: Scenario, trials: int
) -> dict[str, float]:
    samples: dict[str, list[float]] = {name: [] for name in executables}
    names = list(executables)
    for trial in range(trials):
        order = names[trial % len(names) :] + names[: trial % len(names)]
        for name in order:
            samples[name].append(run_once(executables[name], scenario).seconds)
    return {name: statistics.median(values) for name, values in samples.items()}


def memory_profiles(
    executables: dict[str, Path], scenario: Scenario
) -> dict[str, dict[str, int | str]]:
    return {
        name: run_once(executable, scenario, profile=True).values
        for name, executable in executables.items()
    }


def validate_executable(path: str) -> Path:
    executable = Path(path).resolve()
    if not executable.is_file():
        raise argparse.ArgumentTypeError(f"not a file: {path}")
    return executable


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--current", required=True, type=validate_executable)
    parser.add_argument("--uncached", required=True, type=validate_executable)
    parser.add_argument("--cached", required=True, type=validate_executable)
    parser.add_argument("--trials", type=int, default=7)
    args = parser.parse_args()
    if args.trials < 3:
        parser.error("--trials must be at least 3")
    executables = {
        "current": args.current,
        "uncached": args.uncached,
        "cached": args.cached,
    }
    timings: dict[str, dict[str, float]] = {}
    profiles: dict[str, dict[str, dict[str, int | str]]] = {}

    for scenario in SCENARIOS:
        for executable in executables.values():
            run_once(executable, scenario)
        timings[scenario.name] = median_trials(executables, scenario, args.trials)
        profiles[scenario.name] = memory_profiles(executables, scenario)

    print("scenario,operations,current_us,uncached_us,cached_us,current_speedup,cached_overhead")
    for scenario in SCENARIOS:
        result = timings[scenario.name]
        scale = 1_000_000.0 / scenario.iterations
        speedup = result["current"] / result["cached"]
        overhead = result["cached"] / result["uncached"] - 1.0
        print(
            f"{scenario.name},{scenario.iterations},"
            f"{result['current'] * scale:.3f},{result['uncached'] * scale:.3f},"
            f"{result['cached'] * scale:.3f},{speedup:.3f},{overhead:.3%}"
        )

    print("scenario,current_delta,uncached_delta,cached_delta,extra_cached")
    maximum_extra = 0
    for scenario in SCENARIOS:
        deltas: dict[str, int] = {}
        for name in executables:
            values = profiles[scenario.name][name]
            deltas[name] = int(values["peak_bytes"]) - int(values["prepared_bytes"])
        extra = max(0, deltas["cached"] - deltas["uncached"])
        maximum_extra = max(maximum_extra, extra)
        print(
            f"{scenario.name},{deltas['current']},{deltas['uncached']},"
            f"{deltas['cached']},{extra}"
        )

    warm_ok = all(
        timings[name]["current"] / timings[name]["cached"] >= WARM_SPEEDUP_MIN
        for name in ("warm-chain", "session-reset")
    )
    overhead_ok = all(
        timings[name]["cached"] / timings[name]["uncached"] - 1.0 <= REFERENCE_OVERHEAD_MAX
        for name in ("cold-chain", "collisions", "long-chain", "large-batch")
    )
    memory_ok = maximum_extra <= EXTRA_MEMORY_MAX
    decision = "GO" if warm_ok and overhead_ok and memory_ok else "NO-GO"
    print(f"warm_speedup_threshold={WARM_SPEEDUP_MIN:.2f}")
    print(f"reference_overhead_threshold={REFERENCE_OVERHEAD_MAX:.2%}")
    print(f"extra_memory_threshold={EXTRA_MEMORY_MAX}")
    print(f"maximum_extra_cached_bytes={maximum_extra}")
    print(f"warm_speedup_pass={str(warm_ok).lower()}")
    print(f"reference_overhead_pass={str(overhead_ok).lower()}")
    print(f"extra_memory_pass={str(memory_ok).lower()}")
    print(f"decision={decision}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
