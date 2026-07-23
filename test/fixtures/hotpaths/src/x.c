/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "../include/ixsimpl.h"

#define KILL() scan_state()

/* Walks all context state. */
/* scan: ctx */
static void scan_state(void) {}

/* A string literal shaped like a tag must not become one.  If it did,
 * it would attach to helper below and turn it into a scan source. */
static const char *not_a_tag = "/* scan: ctx */";

static void helper(void) { KILL(); }

int ixs_fast(void) {
  helper();
  return 0;
}

int ixs_split(void) { return not_a_tag ? 0 : 1; }

/* Misplaced: a blank line follows, so this must be rejected rather than
 * attach to distant. */
/* hot */

static void distant(void) {}
