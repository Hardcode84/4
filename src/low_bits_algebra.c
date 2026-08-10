/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "low_bits_algebra.h"

#include "simplify.h"
#include <assert.h>
#include <string.h>

typedef struct {
  ixs_node *key;
  ixs_node *value;
  ixs_node *parent;
  uint32_t next_child;
  uint32_t child_count;
} lb_entry;

/* `parent` threads the active DFS stack and value marks completion. An
 * unvalued child with traversal state is therefore an active ancestor/cycle. */

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  lb_entry *entries;
  size_t capacity;
  size_t count;
  unsigned bits;
  ixs_algebra_status status;
} lb_query;

static void lb_note(lb_query *query, ixs_algebra_status status) {
  if (status != IXS_ALGEBRA_MATCH && status > query->status)
    query->status = status;
}

static bool lb_stopped(const lb_query *query) {
  return query->status >= IXS_ALGEBRA_LIMITED;
}

static bool lb_domain(lb_query *query, ixs_node *node) {
  ixs_algebra_status status =
      ixs_bounds_check_integer_domain(query->bounds, node);
  lb_note(query, status);
  return status == IXS_ALGEBRA_MATCH;
}

static lb_entry *lb_slot(const lb_query *query, ixs_node *node) {
  size_t index;
  if (!query->capacity)
    return NULL;
  index = node->hash & (query->capacity - 1u);
  while (query->entries[index].key && query->entries[index].key != node)
    index = (index + 1u) & (query->capacity - 1u);
  return &query->entries[index];
}

/* Expected O(1) lookup keeps traversal O(nodes + edges), plus bounds oracles.
 * Canonical ADD/MUL reconstruction retains O(children^2) worst-case work. */
static bool lb_grow(lb_query *query) {
  size_t next = query->capacity ? query->capacity * 2u : 64u;
  lb_entry *entries;
  size_t i;
  if (next <= query->capacity || next > SIZE_MAX / sizeof(*entries)) {
    lb_note(query, IXS_ALGEBRA_INVALID);
    return false;
  }
  entries = ixs_arena_alloc(&query->ctx->scratch, next * sizeof(*entries),
                            sizeof(void *));
  if (!entries) {
    lb_note(query, IXS_ALGEBRA_OOM);
    return false;
  }
  memset(entries, 0, next * sizeof(*entries));
  for (i = 0; i < query->capacity; i++) {
    if (query->entries[i].key) {
      size_t index = query->entries[i].key->hash & (next - 1u);
      while (entries[index].key)
        index = (index + 1u) & (next - 1u);
      entries[index] = query->entries[i];
    }
  }
  query->entries = entries;
  query->capacity = next;
  return true;
}

static lb_entry *lb_ensure(lb_query *query, ixs_node *node) {
  lb_entry *entry = lb_slot(query, node);
  if (entry && entry->key)
    return entry;
  if ((!query->capacity || query->count >= query->capacity / 2u) &&
      !lb_grow(query))
    return NULL;
  entry = lb_slot(query, node);
  if (!entry->key) {
    entry->key = node;
    query->count++;
  }
  return entry;
}

static bool lb_literal_divisible(ixs_node *node, unsigned bits) {
  return node->tag == IXS_INT && node->u.ival > 0 &&
         (bits == 0u || ((uint64_t)node->u.ival &
                         ((UINT64_C(1) << bits) - UINT64_C(1))) == 0u);
}

static ixs_node *lb_child(ixs_node *node, uint32_t index) {
  if (node->tag == IXS_ADD)
    return node->u.add.terms[index].term;
  if (node->tag == IXS_MUL)
    return node->u.mul.factors[index].base;
  if (node->tag == IXS_MOD)
    return node->u.binary.lhs;
  return node->u.assoc.args[index];
}

static bool lb_propagates(lb_query *query, ixs_node *node, uint32_t *count) {
  uint32_t i;
  *count = 0u;
  if (node->tag == IXS_ADD) {
    if (!ixs_node_is_integer_valued(node->u.add.coeff) ||
        !lb_domain(query, node))
      return false;
    *count = node->u.add.nterms;
    for (i = 0; i < *count; i++)
      if (!ixs_node_is_integer_valued(node->u.add.terms[i].coeff) ||
          !lb_domain(query, node->u.add.terms[i].term))
        return false;
    return *count != 0u;
  }
  if (node->tag == IXS_MUL) {
    if (!ixs_node_is_integer_valued(node->u.mul.coeff) ||
        !lb_domain(query, node))
      return false;
    *count = node->u.mul.nfactors;
    for (i = 0; i < *count; i++)
      if (node->u.mul.factors[i].exp <= 0 ||
          !lb_domain(query, node->u.mul.factors[i].base))
        return false;
    return *count != 0u;
  }
  if (node->tag == IXS_MOD) {
    if (!lb_literal_divisible(node->u.binary.rhs, query->bits) ||
        !lb_domain(query, node) || !lb_domain(query, node->u.binary.lhs))
      return false;
    *count = 1u;
    return true;
  }
  if (node->tag != IXS_XOR && node->tag != IXS_AND && node->tag != IXS_OR)
    return false;
  if (!lb_domain(query, node))
    return false;
  *count = node->u.assoc.nargs;
  for (i = 0; i < *count; i++)
    if (!lb_domain(query, node->u.assoc.args[i]))
      return false;
  return *count != 0u;
}

static ixs_node *lb_rebuild(lb_query *query, const lb_entry *entry) {
  ixs_arena_mark mark;
  ixs_node **targets;
  ixs_node **replacements;
  ixs_node *result = entry->key;
  size_t bytes;
  uint32_t i;
  bool changed = false;
  if (entry->key->tag == IXS_MOD)
    return lb_slot(query, entry->key->u.binary.lhs)->value;
  bytes = (size_t)entry->child_count * sizeof(*targets);
  if (bytes / sizeof(*targets) != entry->child_count || bytes > SIZE_MAX / 2u) {
    lb_note(query, IXS_ALGEBRA_INVALID);
    return NULL;
  }
  mark = ixs_arena_save(&query->ctx->scratch);
  targets = ixs_arena_alloc(&query->ctx->scratch, 2u * bytes, sizeof(void *));
  if (!targets && bytes != 0u) {
    lb_note(query, IXS_ALGEBRA_OOM);
    goto cleanup;
  }
  replacements = targets + entry->child_count;
  for (i = 0; i < entry->child_count; i++) {
    lb_entry *child;
    targets[i] = lb_child(entry->key, i);
    child = lb_slot(query, targets[i]);
    replacements[i] = child->value;
    changed = changed || replacements[i] != targets[i];
  }
  /* Every immediate edge is a target, including opaque unchanged children.
   * Substitution therefore cannot leak through a shared opaque occurrence. */
  if (changed)
    result = simp_subs_multi(query->ctx, entry->key, entry->child_count,
                             targets, replacements);
  if (!result)
    lb_note(query, IXS_ALGEBRA_OOM);
  else if (ixs_node_is_sentinel(result)) {
    lb_note(query, IXS_ALGEBRA_INVALID);
    result = NULL;
  }
cleanup:
  ixs_arena_restore(&query->ctx->scratch, mark);
  return result;
}

static ixs_node *lb_normalize(lb_query *query, ixs_node *root) {
  ixs_node *node = root;
  lb_entry *entry = lb_ensure(query, root);
  if (!entry)
    return NULL;
  while (node && !lb_stopped(query)) {
    ixs_node *child;
    entry = lb_slot(query, node);
    if (!entry->value && entry->child_count == 0u &&
        !lb_propagates(query, node, &entry->child_count))
      entry->value = node;
    if (lb_stopped(query))
      break;
    if (!entry->value && entry->next_child < entry->child_count) {
      child = lb_child(node, entry->next_child);
      entry = lb_ensure(query, child);
      if (!entry)
        break;
      if (entry->value) {
        lb_slot(query, node)->next_child++;
      } else if (entry->child_count != 0u || entry->parent) {
        lb_note(query, IXS_ALGEBRA_INVALID);
      } else {
        entry->parent = node;
        node = child;
      }
      continue;
    }
    if (!entry->value && !(entry->value = lb_rebuild(query, entry)))
      break;
    node = entry->parent;
    /* Parent links are live only while an entry is incomplete. */
    entry->parent = NULL;
    if (node)
      lb_slot(query, node)->next_child++;
  }
  entry = lb_slot(query, root);
  return !lb_stopped(query) && entry ? entry->value : NULL;
}

IXS_STATIC ixs_algebra_status ixs_low_bits_algebra_project(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    unsigned bits, ixs_node **projected_lhs, ixs_node **projected_rhs) {
  lb_query query;
  ixs_arena_mark mark;
  ixs_algebra_status status;
  assert(ctx && bounds && lhs && rhs && projected_lhs && projected_rhs &&
         bits <= 62u);
  memset(&query, 0, sizeof(query));
  query.ctx = ctx;
  query.bounds = bounds;
  query.bits = bits;
  mark = ixs_arena_save(&ctx->scratch);
  *projected_lhs = lb_normalize(&query, lhs);
  *projected_rhs = *projected_lhs ? lb_normalize(&query, rhs) : NULL;
  status = *projected_lhs && *projected_rhs ? IXS_ALGEBRA_MATCH : query.status;
  if (status != IXS_ALGEBRA_MATCH) {
    *projected_lhs = lhs;
    *projected_rhs = rhs;
  }
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}
