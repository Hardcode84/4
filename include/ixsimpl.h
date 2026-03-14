#ifndef IXSIMPL_H
#define IXSIMPL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct ixs_ctx ixs_ctx;
typedef struct ixs_node ixs_node;

typedef enum {
  IXS_CMP_GT,
  IXS_CMP_GE,
  IXS_CMP_LT,
  IXS_CMP_LE,
  IXS_CMP_EQ,
  IXS_CMP_NE
} ixs_cmp_op;

/* --- Context lifecycle --- */

ixs_ctx *ixs_ctx_create(void);
void ixs_ctx_destroy(ixs_ctx *ctx);

/* --- Error list --- */

size_t ixs_ctx_nerrors(ixs_ctx *ctx);
const char *ixs_ctx_error(ixs_ctx *ctx, size_t index);
void ixs_ctx_clear_errors(ixs_ctx *ctx);

/* --- Sentinel checks --- */

bool ixs_is_error(ixs_node *node);
bool ixs_is_parse_error(ixs_node *node);
bool ixs_is_domain_error(ixs_node *node);

/* --- Parse --- */

ixs_node *ixs_parse(ixs_ctx *ctx, const char *input, size_t len);

/* --- Constructors --- */

ixs_node *ixs_int(ixs_ctx *ctx, int64_t val);
ixs_node *ixs_rat(ixs_ctx *ctx, int64_t p, int64_t q);
ixs_node *ixs_sym(ixs_ctx *ctx, const char *name);

ixs_node *ixs_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_neg(ixs_ctx *ctx, ixs_node *a);
ixs_node *ixs_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_floor(ixs_ctx *ctx, ixs_node *x);
ixs_node *ixs_ceil(ixs_ctx *ctx, ixs_node *x);
ixs_node *ixs_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

ixs_node *ixs_pw(ixs_ctx *ctx, uint32_t n, ixs_node **values, ixs_node **conds);

ixs_node *ixs_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_not(ixs_ctx *ctx, ixs_node *a);
ixs_node *ixs_true(ixs_ctx *ctx);
ixs_node *ixs_false(ixs_ctx *ctx);

/* --- Simplification --- */

ixs_node *ixs_simplify(ixs_ctx *ctx, ixs_node *expr,
                       ixs_node *const *assumptions, size_t n_assumptions);

void ixs_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                        ixs_node *const *assumptions, size_t n_assumptions);

/* --- Comparison and substitution --- */

bool ixs_same_node(ixs_node *a, ixs_node *b);

ixs_node *ixs_subs(ixs_ctx *ctx, ixs_node *expr, const char *var,
                   ixs_node *replacement);

/* --- Output --- */

size_t ixs_print(ixs_node *expr, char *buf, size_t bufsize);
size_t ixs_print_c(ixs_node *expr, char *buf, size_t bufsize);

/* --- Introspection --- */

typedef enum {
  IXS_INT,
  IXS_RAT,
  IXS_SYM,
  IXS_ADD,
  IXS_MUL,
  IXS_FLOOR,
  IXS_CEIL,
  IXS_MOD,
  IXS_PIECEWISE,
  IXS_MAX,
  IXS_MIN,
  IXS_XOR,
  IXS_CMP,
  IXS_AND,
  IXS_OR,
  IXS_NOT,
  IXS_TRUE,
  IXS_FALSE,
  IXS_ERROR,
  IXS_PARSE_ERROR
} ixs_tag;

ixs_tag ixs_node_tag(ixs_node *node);
int64_t ixs_node_int_val(ixs_node *node);
uint32_t ixs_node_hash(ixs_node *node);

#ifdef __cplusplus
}
#endif

#endif /* IXSIMPL_H */
