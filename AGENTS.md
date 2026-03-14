# ixsimpl — Index Expression Simplifier

A specialized C library for simplifying integer arithmetic expressions
used in index computation, memory addressing, and loop bound calculation.

<!-- br-agent-instructions-v1 -->

---

## Beads Workflow Integration

This project uses [beads_rust](https://github.com/Dicklesworthstone/beads_rust) (`br`/`bd`) for issue tracking. Issues are stored in `.beads/` and tracked in git.

### Essential Commands

```bash
# View ready issues (unblocked, not deferred)
br ready              # or: bd ready

# List and search
br list --status=open # All open issues
br show <id>          # Full issue details with dependencies
br search "keyword"   # Full-text search

# Create and update
br create --title="..." --description="..." --type=task --priority=2
br update <id> --status=in_progress
br close <id> --reason="Completed"
br close <id1> <id2>  # Close multiple issues at once

# Sync with git
br sync --flush-only  # Export DB to JSONL
br sync --status      # Check sync status
```

### Workflow Pattern

1. **Start**: Run `br ready` to find actionable work
2. **Claim**: Use `br update <id> --status=in_progress`
3. **Work**: Implement the task
4. **Complete**: Use `br close <id>`
5. **Sync**: Always run `br sync --flush-only` at session end

### Key Concepts

- **Dependencies**: Issues can block other issues. `br ready` shows only unblocked work.
- **Priority**: P0=critical, P1=high, P2=medium, P3=low, P4=backlog (use numbers 0-4, not words)
- **Types**: task, bug, feature, epic, chore, docs, question
- **Blocking**: `br dep add <issue> <depends-on>` to add dependencies

### Session Protocol

**Before ending any session, run this checklist:**

```bash
git status              # Check what changed
git add <files>         # Stage code changes (NOT .beads/)
br sync --flush-only    # Export beads changes to JSONL
git commit -m "..."     # Commit code only
git push                # Push to remote
```

**Do NOT commit `.beads/`** — the beads database and JSONL files are local
working state, not source artifacts. The `.beads/` directory should stay in
`.gitignore`.

### Best Practices

- Check `br ready` at session start to find available work
- Update status as you work (in_progress → closed)
- Create new issues with `br create` when you discover tasks
- Use descriptive titles and set appropriate priority/type
- Always sync before ending session
- Never `git add .beads/` — beads are local-only

<!-- end-br-agent-instructions -->

## Design

`DESIGN.md` is the living spec. When code changes invalidate or extend what's described there — API signatures, node types, simplification rules, file structure, performance targets — update `DESIGN.md` in the same commit.

## Language & Build

- **Pedantic C99**. Compile with `-std=c99 -pedantic -Wall -Wextra -Werror`.
- No non-standard extensions (no GCC-isms, no `__attribute__`, no `typeof`, no statement-expressions, no zero-length arrays). If it doesn't compile with a strict C99 compiler, it doesn't ship.
- **Build system: CMake**. No autotools, no plain Makefiles.
- **No global state**. Zero file-scope or static mutable variables in the core library. All state lives in the context (`ixs_ctx`). The library must be safe to use from multiple threads with separate contexts.
- **Arena-only allocation**. All memory is obtained in large 4K-aligned chunks and distributed via arenas. No direct `malloc`/`calloc`/`realloc`/`free` for individual objects.
- **No OS-specific functions**. Only standard C library calls. No `mmap`, no `posix_memalign`, no `VirtualAlloc`, no platform headers. Portable C99 stdlib only.
- **No Unicode**. Only ASCII in source files — code, comments, string literals, all of it.
- **Bounded recursion only**. Every recursive call must have a small, statically provable depth bound. If you can't prove the bound, rewrite it as iteration.

## Tone

Code comments, docstrings, and commit messages share the same voice: terse, dry, informative. Wit is welcome, fluff is not. Say what the thing does, not what you wish it did. If a comment doesn't earn its line, delete it.

## Commits

- Small, focused commits. One logical change per commit. If you're wondering whether to split — split.
- Stage files first, then run `pre-commit` — it only checks staged files. Fix issues and re-stage before committing.
- Sign commits: `git commit -s`.
- Commit messages should be descriptive, or at least funny. Not both is acceptable. Neither is not.
