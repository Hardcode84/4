/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_STORE_H
#define IXS_BOUNDS_STORE_H

#include "bounds.h"

IXS_STATIC bool bounds_store_init(ixs_bounds *bounds, ixs_arena *scratch);
IXS_STATIC void bounds_store_bind(ixs_bounds *bounds, ixs_ctx *ctx,
                                  ixs_arena *scratch);
IXS_STATIC void bounds_store_retarget_scratch(ixs_bounds *bounds,
                                              ixs_arena *scratch);
IXS_STATIC ixs_ctx *bounds_store_swap_active_context(ixs_bounds *bounds,
                                                     ixs_ctx *ctx);
IXS_STATIC bool *bounds_store_swap_change_observer(ixs_bounds *bounds,
                                                   bool *observer);
/* Aggregate fork order is query, begin, var index, difference, inverse,
 * relation, expression, nonzero.  Each phase consumes its predecessors. */
IXS_STATIC bool bounds_store_fork_begin(ixs_bounds *dst, const ixs_bounds *src);
IXS_STATIC bool bounds_store_fork_var_index(ixs_bounds *dst,
                                            const ixs_bounds *src);
IXS_STATIC bool bounds_store_fork_mod_inverse(ixs_bounds *dst,
                                              const ixs_bounds *src);
IXS_STATIC bool bounds_store_fork_expr(ixs_bounds *dst, const ixs_bounds *src);
IXS_STATIC bool bounds_store_fork_nonzero(ixs_bounds *dst,
                                          const ixs_bounds *src);

IXS_STATIC void bounds_store_mark_semantic_changed(ixs_bounds *bounds);
IXS_STATIC void bounds_store_mark_contradiction(ixs_bounds *bounds);
IXS_STATIC void bounds_store_invalidate_reads(ixs_bounds *bounds);
/* Publish one relation insertion result into store-owned latches and caches. */
IXS_STATIC void
bounds_store_publish_relation_status(ixs_bounds *bounds,
                                     ixs_relation_status status);
/* Returned var pointers are borrowed and invalidated by later var insertion or
 * growth.  Published dense indices remain stable. */
IXS_STATIC ixs_var_bound *bounds_store_find_var(ixs_bounds *bounds,
                                                const char *name);
IXS_STATIC bool bounds_store_get_or_create_var_index(ixs_bounds *bounds,
                                                     const char *name,
                                                     size_t *index);
IXS_STATIC ixs_var_bound *bounds_store_get_or_create_var(ixs_bounds *bounds,
                                                         const char *name);
IXS_STATIC void bounds_store_import_var(ixs_bounds *bounds,
                                        ixs_var_bound *destination,
                                        const ixs_var_bound *source);
IXS_STATIC bool bounds_store_set_var_interval(ixs_bounds *bounds,
                                              ixs_var_bound *var,
                                              ixs_interval interval);
IXS_STATIC void bounds_store_refine_var_bits(ixs_bounds *bounds,
                                             ixs_var_bound *var);
IXS_STATIC void bounds_store_apply_var_known_bits(ixs_bounds *bounds,
                                                  ixs_var_bound *var,
                                                  uint64_t known_zero,
                                                  uint64_t known_one);
IXS_STATIC void bounds_store_apply_known_bits(ixs_bounds *bounds,
                                              const char *name,
                                              uint64_t known_zero,
                                              uint64_t known_one);
IXS_STATIC void bounds_store_apply_pow2(ixs_bounds *bounds, ixs_var_bound *var,
                                        ixs_pow2_fact pow2);
IXS_STATIC void bounds_store_apply_exact_int_bits(ixs_bounds *bounds,
                                                  ixs_var_bound *var,
                                                  int64_t value);
/* True means the congruence changed and the caller must propagate difference
 * constraints; it is not a generic success result. */
IXS_STATIC bool bounds_store_merge_modrem(ixs_bounds *bounds, const char *name,
                                          int64_t modulus, int64_t remainder);
IXS_STATIC ixs_interval bounds_store_expr_interval(ixs_bounds *bounds,
                                                   ixs_node *expr);
/* The expression and index may be published before watcher allocation fails;
 * allocation failure latches bounds->oom. */
IXS_STATIC void bounds_store_add_expr_raw(ixs_bounds *bounds, ixs_node *expr,
                                          ixs_interval interval);
IXS_STATIC bool bounds_store_contains_nonzero(const ixs_bounds *bounds,
                                              const ixs_node *expr);
/* False means duplicate/no-op or OOM; bounds->oom distinguishes OOM. */
IXS_STATIC bool bounds_store_add_nonzero(ixs_bounds *bounds, ixs_node *expr);
IXS_STATIC void bounds_store_note_mod_inverse_visit(ixs_bounds *bounds);
IXS_STATIC bool bounds_store_get_modrem(ixs_bounds *bounds, const char *name,
                                        int64_t *modulus, int64_t *remainder);

#endif /* IXS_BOUNDS_STORE_H */
