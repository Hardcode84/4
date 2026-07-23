/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXSIMPL_H
#define IXSIMPL_H

/*
 * Prose: ixs_ghost(x) is reserved for future use.
 * A line-based scanner would mistake it for an API function.
 */
int ixs_fast(void);

/* A declaration split before the parenthesis must still be a root. */
int
ixs_split
(void);

#endif /* IXSIMPL_H */
