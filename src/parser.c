/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "parser.h"
#include "simplify.h"
#include <ctype.h>
#include <limits.h>
#include <string.h>

#define PARSER_MAX_DEPTH 256

typedef struct {
  ixs_ctx *ctx;
  const char *input;
  size_t len;
  size_t pos;
  int depth;
  int max_depth;
} parser;

/* --- Lexer helpers --- */

static void skip_ws(parser *p) {
  while (p->pos < p->len &&
         (p->input[p->pos] == ' ' || p->input[p->pos] == '\t' ||
          p->input[p->pos] == '\n' || p->input[p->pos] == '\r'))
    p->pos++;
}

static bool at_end(parser *p) {
  skip_ws(p);
  return p->pos >= p->len;
}

static char peek(parser *p) {
  skip_ws(p);
  if (p->pos >= p->len)
    return '\0';
  return p->input[p->pos];
}

static bool match_char(parser *p, char c) {
  skip_ws(p);
  if (p->pos < p->len && p->input[p->pos] == c) {
    p->pos++;
    return true;
  }
  return false;
}

static bool match_str(parser *p, const char *s) {
  size_t slen = strlen(s);
  skip_ws(p);
  if (p->pos + slen <= p->len && memcmp(p->input + p->pos, s, slen) == 0) {
    /* Check that the next char isn't alphanumeric (keyword boundary). */
    if (slen > 0 && isalpha((unsigned char)s[slen - 1])) {
      if (p->pos + slen < p->len &&
          (isalnum((unsigned char)p->input[p->pos + slen]) ||
           p->input[p->pos + slen] == '_' || p->input[p->pos + slen] == '$'))
        return false;
    }
    p->pos += slen;
    return true;
  }
  return false;
}

static ixs_node *parse_error(parser *p, const char *msg) {
  ixs_ctx_push_error(p->ctx, "parse error at offset %zu: %s", p->pos, msg);
  return p->ctx->sentinel_parse_error;
}

static bool depth_push(parser *p) {
  if (p->depth >= p->max_depth) {
    ixs_ctx_push_error(p->ctx,
                       "parse error: recursion depth limit (%d) exceeded",
                       p->max_depth);
    return false;
  }
  p->depth++;
  return true;
}

static void depth_pop(parser *p) { p->depth--; }

typedef struct {
  ixs_arena_mark scratch_mark;
  ixs_arena_mark diag_mark;
  const char **errors;
  size_t nerrors;
  size_t errors_cap;
} parser_state;

static void parser_state_save(ixs_ctx *ctx, parser_state *state) {
  state->scratch_mark = ixs_arena_save(&ctx->scratch);
  state->diag_mark = ixs_arena_save(&ctx->diag);
  state->errors = ctx->errors;
  state->nerrors = ctx->nerrors;
  state->errors_cap = ctx->errors_cap;
}

static void parser_state_restore(ixs_ctx *ctx, const parser_state *state) {
  ixs_arena_restore(&ctx->scratch, state->scratch_mark);
  ixs_arena_restore(&ctx->diag, state->diag_mark);
  ctx->errors = state->errors;
  ctx->nerrors = state->nerrors;
  ctx->errors_cap = state->errors_cap;
}

/* --- Forward declarations --- */

static ixs_node *parse_expr(parser *p);
static ixs_node *parse_arith_expr(parser *p);
static ixs_node *parse_cond(parser *p, bool allow_top_level_expr);

/* --- Grammar implementation --- */

static ixs_node *parse_int(parser *p, bool negative) {
  uint64_t limit = negative ? (uint64_t)INT64_MAX + 1u : (uint64_t)INT64_MAX;
  uint64_t magnitude = 0;
  size_t start;

  skip_ws(p);
  start = p->pos;
  if (p->pos >= p->len || !isdigit((unsigned char)p->input[p->pos]))
    return NULL;

  while (p->pos < p->len && isdigit((unsigned char)p->input[p->pos])) {
    uint64_t digit = (uint64_t)(p->input[p->pos] - '0');
    if (magnitude > (limit - digit) / 10u) {
      /* Overflow */
      while (p->pos < p->len && isdigit((unsigned char)p->input[p->pos]))
        p->pos++;
      ixs_ctx_push_error(p->ctx, "integer literal overflow at offset %zu",
                         start);
      return p->ctx->sentinel_error;
    }
    magnitude = magnitude * 10u + digit;
    p->pos++;
  }
  if (!negative)
    return ixs_node_int(p->ctx, (int64_t)magnitude);
  if (magnitude == (uint64_t)INT64_MAX + 1u)
    return ixs_node_int(p->ctx, INT64_MIN);
  return ixs_node_int(p->ctx, -(int64_t)magnitude);
}

static ixs_node *parse_symbol(parser *p) {
  skip_ws(p);
  size_t start = p->pos;
  if (p->pos >= p->len)
    return NULL;

  char c = p->input[p->pos];
  if (!isalpha((unsigned char)c) && c != '_' && c != '$')
    return NULL;

  while (p->pos < p->len) {
    c = p->input[p->pos];
    if (isalnum((unsigned char)c) || c == '_' || c == '$')
      p->pos++;
    else
      break;
  }

  return ixs_node_sym(p->ctx, p->input + start, p->pos - start);
}

static ixs_node *parse_atom(parser *p);

static ixs_node *parse_func_1(parser *p, const char *name) {
  (void)name;
  if (!match_char(p, '('))
    return parse_error(p, "expected '(' after function name");
  ixs_node *arg = parse_expr(p);
  if (!arg)
    return NULL;
  if (!match_char(p, ')'))
    return parse_error(p, "expected ')' after function argument");
  return arg;
}

typedef ixs_node *(*binary_ctor)(ixs_ctx *, ixs_node *, ixs_node *);
typedef ixs_node *(*many_ctor)(ixs_ctx *, uint32_t, ixs_node *const *);

typedef struct {
  ixs_node **args;
  uint32_t nargs;
  size_t cap;
} parser_arg_list;

static bool parser_arg_list_init(parser *p, parser_arg_list *list) {
  list->cap = 8;
  list->nargs = 0;
  list->args = ixs_arena_alloc(&p->ctx->scratch,
                               list->cap * sizeof(*list->args), sizeof(void *));
  return list->args != NULL;
}

static bool parser_arg_list_push(parser *p, parser_arg_list *list,
                                 ixs_node *arg) {
  if ((size_t)list->nargs >= list->cap) {
    size_t old_cap = list->cap;
    size_t new_cap = old_cap * 2u;
    if (new_cap <= old_cap || new_cap > (size_t)-1 / sizeof(*list->args))
      return false;
    list->args = ixs_arena_grow(&p->ctx->scratch, list->args,
                                old_cap * sizeof(*list->args),
                                new_cap * sizeof(*list->args), sizeof(void *));
    if (!list->args)
      return false;
    list->cap = new_cap;
  }
  list->args[list->nargs++] = arg;
  return true;
}

static ixs_node *parse_func_2(parser *p, const char *name, binary_ctor ctor) {
  if (!match_char(p, '('))
    return parse_error(p, "expected '(' after function name");
  ixs_node *a = parse_expr(p);
  if (!a)
    return NULL;
  if (!match_char(p, ','))
    return parse_error(p, "expected ',' in function call");
  ixs_node *b = parse_expr(p);
  if (!b)
    return NULL;
  if (!match_char(p, ')'))
    return parse_error(p, "expected ')' after function arguments");
  (void)name;
  return ctor(p->ctx, a, b);
}

static ixs_node *parse_func_many(parser *p, uint32_t min_args,
                                 const char *arity_error, many_ctor ctor) {
  ixs_arena_mark mark = ixs_arena_save(&p->ctx->scratch);
  parser_arg_list list;
  ixs_node *result = NULL;

  if (!match_char(p, '(')) {
    result = parse_error(p, "expected '(' after function name");
    goto done;
  }
  if (peek(p) == ')') {
    match_char(p, ')');
    result = parse_error(p, arity_error);
    goto done;
  }
  if (!parser_arg_list_init(p, &list))
    goto done;

  for (;;) {
    ixs_node *arg = parse_expr(p);
    if (!arg)
      goto done;
    if (list.nargs == UINT32_MAX) {
      result = parse_error(p, "too many function arguments");
      goto done;
    }
    if (!parser_arg_list_push(p, &list, arg))
      goto done;

    if (match_char(p, ')'))
      break;
    if (!match_char(p, ',')) {
      result = parse_error(p, "expected ',' between function arguments");
      goto done;
    }
    if (peek(p) == ')') {
      result = parse_error(p, "expected function argument after ','");
      goto done;
    }
  }

  if (list.nargs < min_args) {
    result = parse_error(p, arity_error);
    goto done;
  }
  result = ctor(p->ctx, list.nargs, list.args);

done:
  ixs_arena_restore(&p->ctx->scratch, mark);
  return result;
}

static ixs_node *parse_piecewise_impl(parser *p) {
  size_t cap = 16;
  ixs_node **values =
      ixs_arena_alloc(&p->ctx->scratch, cap * sizeof(*values), sizeof(void *));
  ixs_node **conds =
      ixs_arena_alloc(&p->ctx->scratch, cap * sizeof(*conds), sizeof(void *));
  if (!values || !conds)
    return NULL;
  uint32_t n = 0;

  if (!match_char(p, '('))
    return parse_error(p, "expected '(' after Piecewise");

  while (!at_end(p) && peek(p) != ')') {
    if (n > 0 && !match_char(p, ','))
      return parse_error(p, "expected ',' between Piecewise cases");

    if (!match_char(p, '('))
      return parse_error(p, "expected '(' for Piecewise case");

    ixs_node *val = parse_expr(p);
    if (!val)
      return NULL;

    if (!match_char(p, ','))
      return parse_error(p, "expected ',' in Piecewise case");

    ixs_node *cond = parse_cond(p, false);
    if (!cond)
      return NULL;

    if (!match_char(p, ')'))
      return parse_error(p, "expected ')' after Piecewise case");

    if (n >= UINT32_MAX / 2u)
      return parse_error(p, "too many Piecewise cases");
    if (n >= cap) {
      size_t old_cap = cap;
      size_t new_cap = old_cap * 2;
      if (new_cap <= old_cap || new_cap > (size_t)-1 / sizeof(*values))
        return NULL;
      values =
          ixs_arena_grow(&p->ctx->scratch, values, old_cap * sizeof(*values),
                         new_cap * sizeof(*values), sizeof(void *));
      conds = ixs_arena_grow(&p->ctx->scratch, conds, old_cap * sizeof(*conds),
                             new_cap * sizeof(*conds), sizeof(void *));
      if (!values || !conds)
        return NULL;
      cap = new_cap;
    }
    values[n] = val;
    conds[n] = cond;
    n++;
  }

  if (!match_char(p, ')'))
    return parse_error(p, "expected ')' after Piecewise");

  if (n == 0)
    return parse_error(p, "empty Piecewise");

  return simp_pw(p->ctx, n, values, conds);
}

static ixs_node *parse_piecewise(parser *p) {
  ixs_arena_mark m = ixs_arena_save(&p->ctx->scratch);
  ixs_node *result = parse_piecewise_impl(p);
  ixs_arena_restore(&p->ctx->scratch, m);
  return result;
}

static ixs_node *parse_atom(parser *p) {
  ixs_node *result;

  if (!depth_push(p))
    return p->ctx->sentinel_parse_error;

  skip_ws(p);

  /* Parenthesized expression */
  if (peek(p) == '(') {
    match_char(p, '(');
    result = parse_expr(p);
    if (!result) {
      depth_pop(p);
      return NULL;
    }
    if (!match_char(p, ')')) {
      depth_pop(p);
      return parse_error(p, "expected ')'");
    }
    depth_pop(p);
    return result;
  }

  /* Integer literal */
  if (p->pos < p->len && isdigit((unsigned char)p->input[p->pos])) {
    result = parse_int(p, false);
    depth_pop(p);
    return result;
  }

  /* Keywords / functions */
  if (match_str(p, "floor")) {
    result = parse_func_1(p, "floor");
    depth_pop(p);
    return result ? simp_floor(p->ctx, result) : NULL;
  }
  if (match_str(p, "ceiling")) {
    result = parse_func_1(p, "ceiling");
    depth_pop(p);
    return result ? simp_ceil(p->ctx, result) : NULL;
  }
  if (match_str(p, "Trunc")) {
    result = parse_func_1(p, "Trunc");
    depth_pop(p);
    return result ? simp_trunc(p->ctx, result) : NULL;
  }
  if (match_str(p, "Mod")) {
    result = parse_func_2(p, "Mod", simp_mod);
    depth_pop(p);
    return result;
  }
  if (match_str(p, "Max")) {
    result = parse_func_many(p, 1, "Max requires at least one argument",
                             simp_max_many);
    depth_pop(p);
    return result;
  }
  if (match_str(p, "Min")) {
    result = parse_func_many(p, 1, "Min requires at least one argument",
                             simp_min_many);
    depth_pop(p);
    return result;
  }
  if (match_str(p, "xor")) {
    result = parse_func_many(p, 2, "xor requires at least two arguments",
                             simp_xor_many);
    depth_pop(p);
    return result;
  }
  if (match_str(p, "Piecewise")) {
    result = parse_piecewise(p);
    depth_pop(p);
    return result;
  }
  if (match_str(p, "True")) {
    depth_pop(p);
    return p->ctx->node_true;
  }
  if (match_str(p, "False")) {
    depth_pop(p);
    return p->ctx->node_false;
  }

  /* Symbol */
  if (p->pos < p->len) {
    char c = p->input[p->pos];
    if (isalpha((unsigned char)c) || c == '_' || c == '$') {
      result = parse_symbol(p);
      depth_pop(p);
      return result;
    }
  }

  depth_pop(p);
  return parse_error(p, "unexpected token");
}

static ixs_node *parse_unary(parser *p) {
  bool neg = false;
  bool saw_minus = false;
  ixs_node *a;

  skip_ws(p);
  /* Prefix chains are input-length bounded, not grammar-depth bounded. */
  while (peek(p) == '-') {
    match_char(p, '-');
    neg = !neg;
    saw_minus = true;
  }

  skip_ws(p);
  if (saw_minus && p->pos < p->len &&
      isdigit((unsigned char)p->input[p->pos])) {
    if (!depth_push(p))
      return p->ctx->sentinel_parse_error;
    a = parse_int(p, neg);
    depth_pop(p);
    return a;
  }

  a = parse_atom(p);
  if (!a || !neg)
    return a;
  return simp_neg(p->ctx, a);
}

static ixs_node *parse_term(parser *p) {
  ixs_node *left = parse_unary(p);
  if (!left)
    return NULL;

  for (;;) {
    skip_ws(p);
    if (peek(p) == '*') {
      /* Check for ** (power) — not in our grammar, skip. */
      if (p->pos + 1 < p->len && p->input[p->pos + 1] == '*') {
        break; /* Stop, don't consume ** */
      }
      match_char(p, '*');
      ixs_node *right = parse_unary(p);
      if (!right)
        return NULL;
      left = simp_mul(p->ctx, left, right);
      if (!left)
        return NULL;
    } else if (peek(p) == '/') {
      match_char(p, '/');
      ixs_node *right = parse_unary(p);
      if (!right)
        return NULL;
      left = simp_div(p->ctx, left, right);
      if (!left)
        return NULL;
    } else {
      break;
    }
  }
  return left;
}

static ixs_node *parse_arith_expr(parser *p) {
  ixs_node *left = parse_term(p);
  if (!left)
    return NULL;

  for (;;) {
    skip_ws(p);
    if (peek(p) == '+') {
      match_char(p, '+');
      ixs_node *right = parse_term(p);
      if (!right)
        return NULL;
      left = simp_add(p->ctx, left, right);
      if (!left)
        return NULL;
    } else if (peek(p) == '-') {
      match_char(p, '-');
      ixs_node *right = parse_term(p);
      if (!right)
        return NULL;
      left = simp_sub(p->ctx, left, right);
      if (!left)
        return NULL;
    } else {
      break;
    }
  }
  return left;
}

typedef ixs_node *(*operand_parser)(parser *);

static ixs_node *parse_assoc_chain(parser *p, operand_parser parse_operand,
                                   char op, const char *overflow_error,
                                   many_ctor ctor) {
  ixs_node *left = parse_operand(p);
  ixs_arena_mark mark;
  parser_arg_list list;
  ixs_node *result;
  if (!left)
    return NULL;

  if (peek(p) != op)
    return left;

  mark = ixs_arena_save(&p->ctx->scratch);
  if (!parser_arg_list_init(p, &list)) {
    ixs_arena_restore(&p->ctx->scratch, mark);
    return NULL;
  }
  if (!parser_arg_list_push(p, &list, left)) {
    ixs_arena_restore(&p->ctx->scratch, mark);
    return NULL;
  }

  while (peek(p) == op) {
    ixs_node *right;
    match_char(p, op);
    right = parse_operand(p);
    if (!right) {
      ixs_arena_restore(&p->ctx->scratch, mark);
      return NULL;
    }
    if (list.nargs == UINT32_MAX) {
      result = parse_error(p, overflow_error);
      ixs_arena_restore(&p->ctx->scratch, mark);
      return result;
    }
    if (!parser_arg_list_push(p, &list, right)) {
      ixs_arena_restore(&p->ctx->scratch, mark);
      return NULL;
    }
  }
  result = ctor(p->ctx, list.nargs, list.args);
  ixs_arena_restore(&p->ctx->scratch, mark);
  return result;
}

static ixs_node *parse_bitand_expr(parser *p) {
  return parse_assoc_chain(p, parse_arith_expr, '&', "too many '&' operands",
                           simp_and_many);
}

static ixs_node *parse_expr(parser *p) {
  return parse_assoc_chain(p, parse_bitand_expr, '|', "too many '|' operands",
                           simp_or_many);
}

/* --- Condition parsing --- */

static ixs_node *coerce_expr_to_pred(parser *p, ixs_node *node) {
  if (!node || ixs_node_is_sentinel(node) || ixs_node_is_pred_kind(node))
    return node;
  return simp_cmp(p->ctx, node, IXS_CMP_NE, ixs_node_int(p->ctx, 0));
}

static bool parse_cmp_op_token(parser *p, ixs_cmp_op *op) {
  skip_ws(p);
  if (p->pos + 1 < p->len && p->input[p->pos] == '>' &&
      p->input[p->pos + 1] == '=') {
    p->pos += 2;
    *op = IXS_CMP_GE;
    return true;
  }
  if (p->pos + 1 < p->len && p->input[p->pos] == '<' &&
      p->input[p->pos + 1] == '=') {
    p->pos += 2;
    *op = IXS_CMP_LE;
    return true;
  }
  if (p->pos + 1 < p->len && p->input[p->pos] == '=' &&
      p->input[p->pos + 1] == '=') {
    p->pos += 2;
    *op = IXS_CMP_EQ;
    return true;
  }
  if (p->pos + 1 < p->len && p->input[p->pos] == '!' &&
      p->input[p->pos + 1] == '=') {
    p->pos += 2;
    *op = IXS_CMP_NE;
    return true;
  }
  if (p->pos < p->len && p->input[p->pos] == '>') {
    p->pos++;
    *op = IXS_CMP_GT;
    return true;
  }
  if (p->pos < p->len && p->input[p->pos] == '<') {
    p->pos++;
    *op = IXS_CMP_LT;
    return true;
  }
  return false;
}

static bool expr_cmp_would_steal_condition_op(parser *p, size_t start,
                                              size_t end) {
  int parens = 0;
  size_t i;

  for (i = start; i < end; i++) {
    char c = p->input[i];
    if (c == '(') {
      parens++;
    } else if (c == ')') {
      if (parens > 0)
        parens--;
    } else if (parens == 0 && (c == '&' || c == '|')) {
      size_t rhs = i + 1;
      while (rhs < end && (p->input[rhs] == ' ' || p->input[rhs] == '\t' ||
                           p->input[rhs] == '\n' || p->input[rhs] == '\r'))
        rhs++;
      /* Keep legacy flag shorthand like "x | y == 0" as a condition chain.
       * Mask-like spellings such as "x & 3 == 1" still parse bitwise. */
      if (rhs < end && (isalpha((unsigned char)p->input[rhs]) ||
                        p->input[rhs] == '_' || p->input[rhs] == '$'))
        return true;
      return false;
    }
  }
  return false;
}

static ixs_node *try_parse_expr_cmp(parser *p, bool *done) {
  parser_state state;
  size_t start_pos = p->pos;
  size_t cmp_pos;
  int start_depth = p->depth;
  ixs_node *left;
  ixs_node *right;
  ixs_cmp_op op;

  *done = false;
  parser_state_save(p->ctx, &state);

  left = parse_expr(p);
  if (!left) {
    *done = true;
    return NULL;
  }
  if (left->tag == IXS_PARSE_ERROR) {
    parser_state_restore(p->ctx, &state);
    p->pos = start_pos;
    p->depth = start_depth;
    return NULL;
  }

  skip_ws(p);
  cmp_pos = p->pos;
  if (!parse_cmp_op_token(p, &op)) {
    parser_state_restore(p->ctx, &state);
    p->pos = start_pos;
    p->depth = start_depth;
    return NULL;
  }
  if (expr_cmp_would_steal_condition_op(p, start_pos, cmp_pos)) {
    parser_state_restore(p->ctx, &state);
    p->pos = start_pos;
    p->depth = start_depth;
    return NULL;
  }

  right = parse_arith_expr(p);
  if (!right) {
    *done = true;
    return NULL;
  }

  *done = true;
  return simp_cmp(p->ctx, left, op, right);
}

static ixs_node *parse_cmp_expr(parser *p, bool allow_top_level_expr);

static ixs_node *parse_cmp_expr(parser *p, bool allow_top_level_expr) {
  bool saw_not = false;
  bool invert = false;
  bool have_cmp = false;
  ixs_node *result;

  skip_ws(p);

  /* Prefix chains are input-length bounded, not grammar-depth bounded. */
  while (peek(p) == '~') {
    match_char(p, '~');
    saw_not = true;
    invert = !invert;
  }

  result = try_parse_expr_cmp(p, &have_cmp);
  if (have_cmp)
    goto apply_not;

  /* True / False */
  if (match_str(p, "True")) {
    result = p->ctx->node_true;
    goto apply_not;
  }
  if (match_str(p, "False")) {
    result = p->ctx->node_false;
    goto apply_not;
  }

  /* (cond) */
  if (peek(p) == '(') {
    ixs_node *c;
    match_char(p, '(');
    if (!depth_push(p))
      return p->ctx->sentinel_parse_error;
    c = parse_cond(p, allow_top_level_expr);
    if (!c) {
      depth_pop(p);
      return NULL;
    }
    if (!match_char(p, ')')) {
      depth_pop(p);
      return parse_error(p, "expected ')' in condition");
    }
    depth_pop(p);
    result = c;
    goto apply_not;
  }

  /* expr [cmp_op expr] */
  ixs_node *left = parse_arith_expr(p);
  if (!left)
    return NULL;

  skip_ws(p);
  ixs_cmp_op op;

  have_cmp = parse_cmp_op_token(p, &op);

  if (have_cmp) {
    ixs_node *right = parse_arith_expr(p);
    if (!right)
      return NULL;
    result = simp_cmp(p->ctx, left, op, right);
    goto apply_not;
  }

  result =
      allow_top_level_expr && !saw_not ? left : coerce_expr_to_pred(p, left);

apply_not:
  if (!result || !saw_not)
    return result;
  result = coerce_expr_to_pred(p, result);
  if (!result || !invert)
    return result;
  return simp_not(p->ctx, result);
}

static ixs_node *parse_cond_run(parser *p, ixs_node *left, char op) {
  ixs_arena_mark mark = ixs_arena_save(&p->ctx->scratch);
  parser_arg_list list;
  many_ctor ctor = op == '&' ? simp_and_many : simp_or_many;
  ixs_node *result;

  left = coerce_expr_to_pred(p, left);
  if (!left) {
    ixs_arena_restore(&p->ctx->scratch, mark);
    return left;
  }
  if (!parser_arg_list_init(p, &list)) {
    ixs_arena_restore(&p->ctx->scratch, mark);
    return NULL;
  }
  if (!parser_arg_list_push(p, &list, left)) {
    ixs_arena_restore(&p->ctx->scratch, mark);
    return NULL;
  }

  do {
    ixs_node *right;
    match_char(p, op);
    right = parse_cmp_expr(p, false);
    if (!right) {
      ixs_arena_restore(&p->ctx->scratch, mark);
      return NULL;
    }
    right = coerce_expr_to_pred(p, right);
    if (!right) {
      ixs_arena_restore(&p->ctx->scratch, mark);
      return right;
    }
    if (list.nargs == UINT32_MAX) {
      result = parse_error(p, op == '&' ? "too many '&' condition operands"
                                        : "too many '|' condition operands");
      ixs_arena_restore(&p->ctx->scratch, mark);
      return result;
    }
    if (!parser_arg_list_push(p, &list, right)) {
      ixs_arena_restore(&p->ctx->scratch, mark);
      return NULL;
    }
  } while (peek(p) == op);

  result = ctor(p->ctx, list.nargs, list.args);
  ixs_arena_restore(&p->ctx->scratch, mark);
  return result;
}

static ixs_node *parse_cond(parser *p, bool allow_top_level_expr) {
  ixs_node *left = parse_cmp_expr(p, allow_top_level_expr);
  if (!left)
    return NULL;

  while (peek(p) == '&' || peek(p) == '|') {
    char op = peek(p);
    left = parse_cond_run(p, left, op);
    if (!left)
      return left;
  }
  return left;
}

/* --- Public entry point --- */

static ixs_node *parse_full(ixs_ctx *ctx, const char *input, size_t len,
                            bool pred_root) {
  parser p;
  p.ctx = ctx;
  p.input = input;
  p.len = len;
  p.pos = 0;
  p.depth = 0;
  p.max_depth = PARSER_MAX_DEPTH;

  ixs_node *result = pred_root ? parse_cond(&p, true) : parse_expr(&p);
  if (!result)
    return NULL;

  skip_ws(&p);
  if (p.pos < p.len)
    return parse_error(&p, "trailing characters");

  return result;
}

static ixs_node *parse_kind_error(ixs_ctx *ctx, bool expect_pred) {
  ixs_ctx_push_error(ctx, "parse error: expected %s, got %s",
                     expect_pred ? "predicate" : "expression",
                     expect_pred ? "expression" : "predicate");
  return ctx->sentinel_parse_error;
}

static ixs_node *parse_expect_kind(ixs_ctx *ctx, const char *input, size_t len,
                                   bool expect_pred) {
  parser_state orig;
  ixs_node *result;
  bool fallback_pred = !expect_pred;

  parser_state_save(ctx, &orig);
  result = parse_full(ctx, input, len, expect_pred);
  if (!result)
    return NULL;
  if (result->tag == IXS_ERROR)
    return result;
  if (result->tag != IXS_PARSE_ERROR) {
    if ((expect_pred && ixs_node_is_pred_kind(result)) ||
        (!expect_pred && ixs_node_is_expr_kind(result)))
      return result;
    parser_state_restore(ctx, &orig);
    return parse_kind_error(ctx, expect_pred);
  }

  parser_state_restore(ctx, &orig);
  result = parse_full(ctx, input, len, fallback_pred);
  if (!result)
    return NULL;
  if (result->tag == IXS_ERROR)
    return result;
  if (result->tag != IXS_PARSE_ERROR &&
      ((fallback_pred && ixs_node_is_pred_kind(result)) ||
       (!fallback_pred && ixs_node_is_expr_kind(result))))
    return parse_kind_error(ctx, expect_pred);

  parser_state_restore(ctx, &orig);
  return parse_full(ctx, input, len, expect_pred);
}

IXS_STATIC ixs_node *ixs_parse_impl(ixs_ctx *ctx, const char *input,
                                    size_t len) {
  return parse_expect_kind(ctx, input, len, false);
}

IXS_STATIC ixs_node *ixs_parse_expr_impl(ixs_ctx *ctx, const char *input,
                                         size_t len) {
  return ixs_parse_impl(ctx, input, len);
}

IXS_STATIC ixs_node *ixs_parse_pred_impl(ixs_ctx *ctx, const char *input,
                                         size_t len) {
  return parse_expect_kind(ctx, input, len, true);
}
