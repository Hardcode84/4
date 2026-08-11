/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "print.h"
#include "arena.h"
#include <stdio.h>
#include <string.h>

/*
 * snprintf-style accumulator: tracks position and remaining space.
 */
typedef struct {
  char *buf;
  size_t size;
  size_t pos; /* total chars written (may exceed size) */
} printbuf;

static void pb_init(printbuf *pb, char *buf, size_t size) {
  pb->buf = buf;
  pb->size = size;
  pb->pos = 0;
}

static void pb_write(printbuf *pb, const char *s, size_t len) {
  if (pb->buf && pb->pos < pb->size) {
    size_t avail = pb->size - pb->pos;
    size_t n = len < avail ? len : avail;
    memcpy(pb->buf + pb->pos, s, n);
  }
  pb->pos += len;
}

static void pb_str(printbuf *pb, const char *s) { pb_write(pb, s, strlen(s)); }

static void pb_char(printbuf *pb, char c) { pb_write(pb, &c, 1); }

static void pb_i64(printbuf *pb, int64_t v) {
  char tmp[32];
  int n = snprintf(tmp, sizeof(tmp), "%lld", (long long)v);
  pb_write(pb, tmp, (size_t)n);
}

static void pb_finish(printbuf *pb) {
  if (pb->buf && pb->size > 0) {
    size_t end = pb->pos < pb->size ? pb->pos : pb->size - 1;
    pb->buf[end] = '\0';
  }
}

/* Precedence levels for minimal parenthesization. */
typedef enum {
  PREC_ATOM = 0,
  PREC_MUL = 1,
  PREC_ADD = 2,
  PREC_CMP = 3,
  PREC_NOT = 4,
  PREC_AND = 5,
  PREC_OR = 6,
  PREC_TOP = 7
} prec_t;

static prec_t node_prec(const ixs_node *n) {
  switch (n->tag) {
  case IXS_ADD:
    return PREC_ADD;
  case IXS_MUL:
    return PREC_MUL;
  case IXS_CMP:
    return PREC_CMP;
  case IXS_AND:
    return PREC_AND;
  case IXS_OR:
    return PREC_OR;
  case IXS_NOT:
    return PREC_NOT;
  default:
    return PREC_ATOM;
  }
}

static const char *cmp_op_str(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return " > ";
  case IXS_CMP_GE:
    return " >= ";
  case IXS_CMP_LT:
    return " < ";
  case IXS_CMP_LE:
    return " <= ";
  case IXS_CMP_EQ:
    return " == ";
  case IXS_CMP_NE:
    return " != ";
  }
  return "??";
}

typedef enum {
  PRINT_NODE,
  PRINT_WRAPPED,
  PRINT_C_NODE,
  PRINT_C_WRAPPED,
  PRINT_TEXT,
  PRINT_CHAR,
  PRINT_I64,
  PRINT_RAT
} print_action_kind;

typedef struct {
  print_action_kind kind;
  const ixs_node *node;
  const char *text;
  int64_t p;
  int64_t q;
  prec_t prec;
} print_action;

typedef struct {
  ixs_arena arena;
  print_action *actions;
  size_t count;
  size_t capacity;
  printbuf output;
} print_state;

#define PRINT_INLINE_ACTIONS 32u

static bool print_push(print_state *state, print_action action) {
  if (state->count == state->capacity) {
    size_t capacity =
        state->capacity ? state->capacity * 2u : PRINT_INLINE_ACTIONS;
    print_action *grown;
    if (capacity <= state->capacity ||
        capacity > SIZE_MAX / sizeof(*state->actions))
      return false;
    grown = ixs_arena_grow(&state->arena, state->actions,
                           state->capacity * sizeof(*state->actions),
                           capacity * sizeof(*state->actions), sizeof(void *));
    if (!grown)
      return false;
    state->actions = grown;
    state->capacity = capacity;
  }
  state->actions[state->count++] = action;
  return true;
}

static bool print_push_node(print_state *state, const ixs_node *node,
                            prec_t prec, bool c_mode, bool wrapped) {
  print_action action;
  memset(&action, 0, sizeof(action));
  action.kind = c_mode ? (wrapped ? PRINT_C_WRAPPED : PRINT_C_NODE)
                       : (wrapped ? PRINT_WRAPPED : PRINT_NODE);
  action.node = node;
  action.prec = prec;
  return print_push(state, action);
}

static bool print_push_text(print_state *state, const char *text) {
  print_action action;
  memset(&action, 0, sizeof(action));
  action.kind = PRINT_TEXT;
  action.text = text;
  return print_push(state, action);
}

static bool print_push_char(print_state *state, char value) {
  print_action action;
  memset(&action, 0, sizeof(action));
  action.kind = PRINT_CHAR;
  action.p = value;
  return print_push(state, action);
}

static bool print_push_i64(print_state *state, int64_t value) {
  print_action action;
  memset(&action, 0, sizeof(action));
  action.kind = PRINT_I64;
  action.p = value;
  return print_push(state, action);
}

static bool print_push_rat(print_state *state, int64_t p, int64_t q) {
  print_action action;
  memset(&action, 0, sizeof(action));
  action.kind = PRINT_RAT;
  action.p = p;
  action.q = q;
  return print_push(state, action);
}

static bool print_push_unary(print_state *state, const char *name,
                             const ixs_node *arg, bool c_mode) {
  return print_push_char(state, ')') &&
         print_push_node(state, arg, PREC_TOP, c_mode, false) &&
         print_push_char(state, '(') && print_push_text(state, name);
}

static bool print_push_binary(print_state *state, const char *name,
                              const ixs_node *node, bool c_mode) {
  return print_push_char(state, ')') &&
         print_push_node(state, node->u.binary.rhs, PREC_TOP, c_mode, false) &&
         print_push_text(state, ", ") &&
         print_push_node(state, node->u.binary.lhs, PREC_TOP, c_mode, false) &&
         print_push_char(state, '(') && print_push_text(state, name);
}

static bool print_push_assoc_function(print_state *state, const ixs_node *node,
                                      const char *name) {
  uint32_t i;
  if (!print_push_char(state, ')'))
    return false;
  for (i = node->u.assoc.nargs; i > 0; i--) {
    if (!print_push_node(state, node->u.assoc.args[i - 1u], PREC_TOP, false,
                         false) ||
        (i > 1u && !print_push_text(state, ", ")))
      return false;
  }
  return print_push_char(state, '(') && print_push_text(state, name);
}

static bool print_push_assoc_infix(print_state *state, const ixs_node *node,
                                   const char *separator, prec_t prec,
                                   bool c_mode) {
  uint32_t i;
  for (i = node->u.assoc.nargs; i > 0; i--) {
    if (!print_push_node(state, node->u.assoc.args[i - 1u], prec, c_mode,
                         true) ||
        (i > 1u && !print_push_text(state, separator)))
      return false;
  }
  return true;
}

static bool print_push_add_term(print_state *state, const ixs_addterm *term,
                                bool first) {
  int64_t p, q;
  int64_t positive_p, positive_q;
  bool negative;
  ixs_node_get_rat(term->coeff, &p, &q);
  negative = ixs_rat_is_neg(p);
  positive_p = p;
  positive_q = q;
  if (negative)
    ixs_rat_neg(p, q, &positive_p, &positive_q);
  if (!print_push_node(state, term->term,
                       first && !negative && p == 1 && q == 1 ? PREC_ADD
                                                              : PREC_MUL,
                       false, true))
    return false;
  if (!(positive_p == 1 && positive_q == 1) &&
      (!print_push_char(state, '*') ||
       !print_push_rat(state, positive_p, positive_q)))
    return false;
  if (first)
    return !negative || print_push_char(state, '-');
  return print_push_text(state, negative ? " - " : " + ");
}

static bool print_push_add(print_state *state, const ixs_node *node) {
  uint32_t i;
  int64_t constant_p, constant_q;
  bool has_constant;
  ixs_node_get_rat(node->u.add.coeff, &constant_p, &constant_q);
  has_constant = !ixs_rat_is_zero(constant_p);
  if (!has_constant && node->u.add.nterms == 0)
    return print_push_char(state, '0');
  for (i = node->u.add.nterms; i > 0; i--)
    if (!print_push_add_term(state, &node->u.add.terms[i - 1u],
                             !has_constant && i == 1u))
      return false;
  return !has_constant ||
         print_push_node(state, node->u.add.coeff, PREC_ADD, false, false);
}

static bool print_push_mul_factor(print_state *state,
                                  const ixs_mulfactor *factor, bool separator) {
  if (factor->exp == 1) {
    if (!print_push_node(state, factor->base, PREC_MUL, false, true))
      return false;
  } else if (factor->exp == -1) {
    if (!print_push_node(state, factor->base, PREC_MUL, false, true) ||
        !print_push_text(state, "1/"))
      return false;
  } else if (!print_push_i64(state, factor->exp) ||
             !print_push_text(state, "**") ||
             !print_push_node(state, factor->base, PREC_ATOM, false, true)) {
    return false;
  }
  return !separator || print_push_char(state, '*');
}

static bool print_push_mul(print_state *state, const ixs_node *node) {
  uint32_t i;
  int64_t coefficient_p, coefficient_q;
  bool coefficient;
  ixs_node_get_rat(node->u.mul.coeff, &coefficient_p, &coefficient_q);
  coefficient = !(coefficient_p == 1 && coefficient_q == 1) &&
                !(coefficient_p == -1 && coefficient_q == 1);
  for (i = node->u.mul.nfactors; i > 0; i--)
    if (!print_push_mul_factor(state, &node->u.mul.factors[i - 1u],
                               coefficient || i > 1u))
      return false;
  if (coefficient)
    return print_push_node(state, node->u.mul.coeff, PREC_MUL, false, false);
  return coefficient_p != -1 || coefficient_q != 1 ||
         print_push_char(state, '-');
}

static bool print_push_piecewise(print_state *state, const ixs_node *node) {
  uint32_t i;
  if (!print_push_char(state, ')'))
    return false;
  for (i = node->u.pw.ncases; i > 0; i--) {
    const ixs_node *condition = node->u.pw.cases[i - 1u].cond;
    if (!print_push_char(state, ')'))
      return false;
    if (ixs_node_is_known_true(condition)) {
      if (!print_push_text(state, "True"))
        return false;
    } else if (ixs_node_is_known_false(condition)) {
      if (!print_push_text(state, "False"))
        return false;
    } else if (!print_push_node(state, condition, PREC_TOP, false, false)) {
      return false;
    }
    if (!print_push_text(state, ", ") ||
        !print_push_node(state, node->u.pw.cases[i - 1u].value, PREC_TOP, false,
                         false) ||
        !print_push_char(state, '(') ||
        (i > 1u && !print_push_text(state, ", ")))
      return false;
  }
  return print_push_text(state, "Piecewise(");
}

static bool print_expand_node(print_state *state, const ixs_node *node,
                              prec_t parent_prec) {
  if (!node)
    return print_push_text(state, "<null>");
  switch (node->tag) {
  case IXS_INT:
    return print_push_i64(state, node->u.ival);
  case IXS_RAT:
    return print_push_rat(state, node->u.rat.p, node->u.rat.q);
  case IXS_SYM:
    return print_push_text(state, node->u.name);
  case IXS_ADD:
    return print_push_add(state, node);
  case IXS_MUL:
    return print_push_mul(state, node);
  case IXS_FLOOR:
    return print_push_unary(state, "floor", node->u.unary.arg, false);
  case IXS_CEIL:
    return print_push_unary(state, "ceiling", node->u.unary.arg, false);
  case IXS_TRUNC:
    return print_push_unary(state, "Trunc", node->u.unary.arg, false);
  case IXS_MOD:
    return print_push_binary(state, "Mod", node, false);
  case IXS_MAX:
    return print_push_assoc_function(state, node, "Max");
  case IXS_MIN:
    return print_push_assoc_function(state, node, "Min");
  case IXS_XOR:
    return print_push_assoc_function(state, node, "xor");
  case IXS_CMP:
    return print_push_node(state, node->u.binary.rhs, PREC_CMP, false, true) &&
           print_push_text(state, cmp_op_str(node->u.binary.cmp_op)) &&
           print_push_node(state, node->u.binary.lhs, PREC_CMP, false, true);
  case IXS_PIECEWISE:
    return print_push_piecewise(state, node);
  case IXS_AND:
    return print_push_assoc_infix(state, node, " & ", PREC_AND, false);
  case IXS_OR:
    return print_push_assoc_infix(state, node, " | ", PREC_OR, false);
  case IXS_NOT:
    return print_push_node(state, node->u.unary_bool.arg, PREC_NOT, false,
                           true) &&
           print_push_char(state, '~');
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return print_push_text(state, "<error>");
  }
  (void)parent_prec;
  return false;
}

static bool print_push_c_assoc_call(print_state *state, const ixs_node *node,
                                    const char *name) {
  uint32_t i;
  if (node->u.assoc.nargs == 0)
    return print_push_text(state, "()") && print_push_text(state, name);
  for (i = node->u.assoc.nargs; i > 1u; i--)
    if (!print_push_char(state, ')') ||
        !print_push_node(state, node->u.assoc.args[i - 1u], PREC_TOP, true,
                         false) ||
        !print_push_text(state, ", "))
      return false;
  if (!print_push_node(state, node->u.assoc.args[0], PREC_TOP, true, false))
    return false;
  for (i = 1; i < node->u.assoc.nargs; i++)
    if (!print_push_char(state, '(') || !print_push_text(state, name))
      return false;
  return true;
}

static bool print_c_assoc_tag(ixs_tag tag) {
  switch (tag) {
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return true;
  default:
    return false;
  }
}

static bool print_expand_c_assoc(print_state *state, const ixs_node *node) {
  switch (node->tag) {
  case IXS_MAX:
    return print_push_c_assoc_call(state, node, "ixs_max_i");
  case IXS_MIN:
    return print_push_c_assoc_call(state, node, "ixs_min_i");
  case IXS_XOR:
    return print_push_char(state, ')') &&
           print_push_assoc_infix(state, node, " ^ ", PREC_ATOM, true) &&
           print_push_char(state, '(');
  case IXS_AND:
    return print_push_char(state, ')') &&
           print_push_assoc_infix(state, node, " & ", PREC_ATOM, true) &&
           print_push_char(state, '(');
  case IXS_OR:
    return print_push_char(state, ')') &&
           print_push_assoc_infix(state, node, " | ", PREC_ATOM, true) &&
           print_push_char(state, '(');
  default:
    return false;
  }
}

static bool print_expand_c_node(print_state *state, const ixs_node *node,
                                prec_t parent_prec) {
  if (!node)
    return print_push_text(state, "/*null*/0");
  if (print_c_assoc_tag(node->tag))
    return print_expand_c_assoc(state, node);
  switch (node->tag) {
  case IXS_INT:
    return print_push_i64(state, node->u.ival);
  case IXS_RAT:
    return print_push_char(state, ')') && print_push_text(state, ".0") &&
           print_push_i64(state, node->u.rat.q) &&
           print_push_text(state, "/") && print_push_text(state, ".0") &&
           print_push_i64(state, node->u.rat.p) && print_push_char(state, '(');
  case IXS_SYM:
    return print_push_text(state, node->u.name);
  case IXS_FLOOR:
    return print_push_unary(state, "ixs_floor_i", node->u.unary.arg, true);
  case IXS_CEIL:
    return print_push_unary(state, "ixs_ceil_i", node->u.unary.arg, true);
  case IXS_TRUNC:
    return print_push_unary(state, "ixs_trunc_i", node->u.unary.arg, true);
  case IXS_MOD:
    return print_push_binary(state, "ixs_mod_i", node, true);
  default:
    return print_push_node(state, node, parent_prec, false, false);
  }
}

/* Each action either writes a scalar token or expands one node into a bounded
 * number of later actions. The transient arena makes traversal O(nodes and
 * edges) without tying public print depth to the C stack. */
static size_t print_iterative(const ixs_node *expr, char *buf, size_t bufsize,
                              bool c_mode) {
  print_action inline_actions[PRINT_INLINE_ACTIONS];
  print_state state;
  bool ok;
  if (!expr) {
    if (buf && bufsize > 0)
      buf[0] = '\0';
    return 0;
  }
  memset(&state, 0, sizeof(state));
  ixs_arena_init(&state.arena, IXS_ARENA_DEFAULT_SIZE);
  state.actions = inline_actions;
  state.capacity = PRINT_INLINE_ACTIONS;
  pb_init(&state.output, buf, bufsize);
  ok = print_push_node(&state, expr, PREC_TOP, c_mode, false);
  while (ok && state.count != 0) {
    print_action action = state.actions[--state.count];
    switch (action.kind) {
    case PRINT_NODE:
      ok = print_expand_node(&state, action.node, action.prec);
      break;
    case PRINT_WRAPPED:
    case PRINT_C_WRAPPED:
      if (node_prec(action.node) > action.prec)
        ok = print_push_char(&state, ')') &&
             print_push_node(&state, action.node, PREC_TOP,
                             action.kind == PRINT_C_WRAPPED, false) &&
             print_push_char(&state, '(');
      else
        ok = print_push_node(&state, action.node, action.prec,
                             action.kind == PRINT_C_WRAPPED, false);
      break;
    case PRINT_C_NODE:
      ok = print_expand_c_node(&state, action.node, action.prec);
      break;
    case PRINT_TEXT:
      pb_str(&state.output, action.text);
      break;
    case PRINT_CHAR:
      pb_char(&state.output, (char)action.p);
      break;
    case PRINT_I64:
      pb_i64(&state.output, action.p);
      break;
    case PRINT_RAT:
      pb_i64(&state.output, action.p);
      if (action.q != 1) {
        pb_char(&state.output, '/');
        pb_i64(&state.output, action.q);
      }
      break;
    }
  }
  if (!ok) {
    if (buf && bufsize > 0)
      buf[0] = '\0';
    state.output.pos = SIZE_MAX;
  } else {
    pb_finish(&state.output);
  }
  ixs_arena_destroy_transient(&state.arena);
  return state.output.pos;
}

IXS_STATIC size_t ixs_print_impl(const ixs_node *expr, char *buf,
                                 size_t bufsize) {
  return print_iterative(expr, buf, bufsize, false);
}

IXS_STATIC size_t ixs_print_c_impl(const ixs_node *expr, char *buf,
                                   size_t bufsize) {
  return print_iterative(expr, buf, bufsize, true);
}
