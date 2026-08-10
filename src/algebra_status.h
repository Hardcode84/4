/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_ALGEBRA_STATUS_H
#define IXS_ALGEBRA_STATUS_H

/* Failure values are ordered by transport priority. Query state never stores
 * MATCH; result APIs use it only after every required proof is clean. */
typedef enum {
  IXS_ALGEBRA_NO_MATCH,
  IXS_ALGEBRA_MATCH,
  IXS_ALGEBRA_UNREPRESENTABLE,
  IXS_ALGEBRA_LIMITED,
  IXS_ALGEBRA_OOM,
  IXS_ALGEBRA_INVALID
} ixs_algebra_status;

#endif /* IXS_ALGEBRA_STATUS_H */
