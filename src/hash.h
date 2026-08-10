/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_HASH_H
#define IXS_HASH_H

#include <stddef.h>
#include <stdint.h>

static inline size_t ixs_hash_ptr(const void *ptr) {
  uint64_t value = (uint64_t)(uintptr_t)ptr;
  value ^= value >> 33;
  value *= UINT64_C(0xff51afd7ed558ccd);
  value ^= value >> 33;
  return (size_t)value;
}

#endif /* IXS_HASH_H */
