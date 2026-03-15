#include "node.h"

static ixs_node *walk_pre(ixs_node *node, ixs_visit_fn fn, void *ud) {
  ixs_walk_action act = fn(node, ud);
  if (act == IXS_WALK_STOP)
    return node;
  if (act == IXS_WALK_SKIP)
    return NULL;

  uint32_t i;
  ixs_node *stopped;
  switch (node->tag) {
  case IXS_ADD:
    stopped = walk_pre(node->u.add.coeff, fn, ud);
    if (stopped)
      return stopped;
    for (i = 0; i < node->u.add.nterms; i++) {
      stopped = walk_pre(node->u.add.terms[i].coeff, fn, ud);
      if (stopped)
        return stopped;
      stopped = walk_pre(node->u.add.terms[i].term, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_MUL:
    stopped = walk_pre(node->u.mul.coeff, fn, ud);
    if (stopped)
      return stopped;
    for (i = 0; i < node->u.mul.nfactors; i++) {
      stopped = walk_pre(node->u.mul.factors[i].base, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_FLOOR:
  case IXS_CEIL:
    stopped = walk_pre(node->u.unary.arg, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_NOT:
    stopped = walk_pre(node->u.unary_bool.arg, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    stopped = walk_pre(node->u.binary.lhs, fn, ud);
    if (stopped)
      return stopped;
    stopped = walk_pre(node->u.binary.rhs, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_PIECEWISE:
    for (i = 0; i < node->u.pw.ncases; i++) {
      stopped = walk_pre(node->u.pw.cases[i].value, fn, ud);
      if (stopped)
        return stopped;
      stopped = walk_pre(node->u.pw.cases[i].cond, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_AND:
  case IXS_OR:
    for (i = 0; i < node->u.logic.nargs; i++) {
      stopped = walk_pre(node->u.logic.args[i], fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  default:
    break;
  }
  return NULL;
}

static ixs_node *walk_post(ixs_node *node, ixs_visit_fn fn, void *ud) {
  uint32_t i;
  ixs_node *stopped;
  switch (node->tag) {
  case IXS_ADD:
    stopped = walk_post(node->u.add.coeff, fn, ud);
    if (stopped)
      return stopped;
    for (i = 0; i < node->u.add.nterms; i++) {
      stopped = walk_post(node->u.add.terms[i].coeff, fn, ud);
      if (stopped)
        return stopped;
      stopped = walk_post(node->u.add.terms[i].term, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_MUL:
    stopped = walk_post(node->u.mul.coeff, fn, ud);
    if (stopped)
      return stopped;
    for (i = 0; i < node->u.mul.nfactors; i++) {
      stopped = walk_post(node->u.mul.factors[i].base, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_FLOOR:
  case IXS_CEIL:
    stopped = walk_post(node->u.unary.arg, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_NOT:
    stopped = walk_post(node->u.unary_bool.arg, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    stopped = walk_post(node->u.binary.lhs, fn, ud);
    if (stopped)
      return stopped;
    stopped = walk_post(node->u.binary.rhs, fn, ud);
    if (stopped)
      return stopped;
    break;
  case IXS_PIECEWISE:
    for (i = 0; i < node->u.pw.ncases; i++) {
      stopped = walk_post(node->u.pw.cases[i].value, fn, ud);
      if (stopped)
        return stopped;
      stopped = walk_post(node->u.pw.cases[i].cond, fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  case IXS_AND:
  case IXS_OR:
    for (i = 0; i < node->u.logic.nargs; i++) {
      stopped = walk_post(node->u.logic.args[i], fn, ud);
      if (stopped)
        return stopped;
    }
    break;
  default:
    break;
  }

  ixs_walk_action act = fn(node, ud);
  if (act == IXS_WALK_STOP)
    return node;
  return NULL;
}

ixs_node *ixs_walk_pre(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                       void *userdata) {
  (void)ctx;
  if (!root)
    return NULL;
  ixs_node *stopped = walk_pre(root, fn, userdata);
  return stopped ? stopped : root;
}

ixs_node *ixs_walk_post(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                        void *userdata) {
  (void)ctx;
  if (!root)
    return NULL;
  ixs_node *stopped = walk_post(root, fn, userdata);
  return stopped ? stopped : root;
}
