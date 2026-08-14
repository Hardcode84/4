/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_DIVISION_ALGEBRA_H
#define IXS_DIVISION_ALGEBRA_H

#include "algebra_status.h"
#include "bounds.h"

typedef enum {
  IXS_DIVISION_PROJECT_ALL,
  IXS_DIVISION_PROJECT_DIRECT_ONLY,
  IXS_DIVISION_PROJECT_PIECEWISE_REDUCING
} ixs_division_projection_mode;

typedef struct {
  ixs_algebra_status status;
  ixs_node *lhs, *rhs;
} ixs_division_projection_result;

typedef struct {
  ixs_algebra_status status;
  ixs_interval range;
} ixs_division_range_result;

/* ROOT must be a semantics-preserving bounds normalization of SOURCE. A
 * projection need only agree on defined SOURCE evaluations; poison outside
 * that domain may refine to any value. MATCH initializes both output roots.
 * Other semantic misses preserve the input ROOT pointers; transport failures
 * abort the owning proof. Candidate UNREPRESENTABLE does not stop independent
 * discovery and is reported when no complete projection produces a MATCH.
 * Candidate storage grows in scratch with no semantic cap.
 * Discovery, global descendant filtering, and cost walks are expected
 * O(N + E + C) in distinct nodes, edges, and admitted certificates.
 * Substitution delegates canonical ADD/MUL rebuild and its O(children^2)
 * worst case to the simplifier. */
IXS_STATIC ixs_division_projection_result ixs_division_algebra_project(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *source_lhs, ixs_node *root_lhs,
    ixs_node *source_rhs, ixs_node *root_rhs,
    ixs_division_projection_mode mode);

/* Recognize an immediate N - D*Q + shift row and return the signed-truncation
 * remainder radius shifted by its exact integer constant. source_defined means
 * the caller already proved SOURCE over its whole domain; otherwise this query
 * proves SOURCE itself. Recognition scans immediate terms/factors once, then
 * reconstructs its exact integer shift once and invokes the documented bounds
 * oracles. */
IXS_STATIC ixs_division_range_result
ixs_division_algebra_range(ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *source,
                           ixs_node *root, bool source_defined);

#endif /* IXS_DIVISION_ALGEBRA_H */
