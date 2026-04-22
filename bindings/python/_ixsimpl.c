/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * CPython extension module for ixsimpl.
 *
 * Exposes two types: Context (wraps ixs_ctx) and Expr (wraps ixs_node).
 * Operator overloading lets you build expression trees naturally:
 *   x = ctx.sym("x"); e = ixsimpl.floor(x + 3)
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <ixsimpl.h>
#include <string.h>

/* Forward declarations */
static PyTypeObject ContextType;
static PyTypeObject _ExprType;

/* Module-level type used by Expr_wrap to allocate instances.
 * Defaults to &_ExprType; overridden by _set_expr_class() so that a
 * Python subclass (with __dict__) is instantiated instead. */
static PyTypeObject *expr_wrap_type;

/* ------------------------------------------------------------------ */
/*  ContextObject (defined first so ExprObject can reference it)      */
/* ------------------------------------------------------------------ */

typedef struct ContextObject {
  PyObject_HEAD ixs_ctx *ctx;
  ixs_session session;
} ContextObject;

/* ------------------------------------------------------------------ */
/*  ExprObject                                                        */
/* ------------------------------------------------------------------ */

typedef struct ExprObject {
  PyObject_HEAD ixs_node *node;
  ContextObject *ctx_obj;
} ExprObject;

static ExprObject *Expr_wrap(ContextObject *ctx_obj, ixs_node *node) {
  ExprObject *self;
  if (!node) {
    PyErr_SetString(PyExc_MemoryError, "ixsimpl: out of memory");
    return NULL;
  }
  self = (ExprObject *)expr_wrap_type->tp_alloc(expr_wrap_type, 0);
  if (!self)
    return NULL;
  self->node = node;
  self->ctx_obj = ctx_obj;
  Py_INCREF(ctx_obj);
  return self;
}

static ixs_session *Context_session(ContextObject *ctx_obj) {
  return &ctx_obj->session;
}

typedef struct {
  PyObject *buf_obj;
} BytesWriterState;

typedef struct {
  const unsigned char *data;
  Py_ssize_t len;
  Py_ssize_t pos;
} BytesReaderState;

static bool BytesWriter_write(void *userdata, const void *buf, size_t len) {
  BytesWriterState *state = (BytesWriterState *)userdata;
  Py_ssize_t old_len;
  Py_ssize_t new_len;

  if (len == 0)
    return true;
  if (len > (size_t)PY_SSIZE_T_MAX) {
    PyErr_NoMemory();
    return false;
  }

  old_len = PyByteArray_GET_SIZE(state->buf_obj);
  if ((size_t)(PY_SSIZE_T_MAX - old_len) < len) {
    PyErr_NoMemory();
    return false;
  }
  new_len = old_len + (Py_ssize_t)len;
  if (PyByteArray_Resize(state->buf_obj, new_len) < 0)
    return false;

  memcpy(PyByteArray_AS_STRING(state->buf_obj) + old_len, buf, len);
  return true;
}

static bool BytesReader_read(void *userdata, void *buf, size_t len) {
  BytesReaderState *state = (BytesReaderState *)userdata;
  Py_ssize_t remaining;

  if (state->pos > state->len)
    return false;
  remaining = state->len - state->pos;
  if (len > (size_t)remaining)
    return false;
  memcpy(buf, state->data + state->pos, len);
  state->pos += (Py_ssize_t)len;
  return true;
}

static size_t BytesReader_remaining(void *userdata) {
  BytesReaderState *state = (BytesReaderState *)userdata;
  if (state->pos > state->len)
    return 0;
  return (size_t)(state->len - state->pos);
}

static void Expr_dealloc(ExprObject *self) {
  Py_XDECREF(self->ctx_obj);
  Py_TYPE(self)->tp_free((PyObject *)self);
}

/* Coerce a Python object to an ixs_node, extracting ctx from peer Expr. */
static ixs_node *coerce_arg(ContextObject *ctx_obj, PyObject *obj) {
  if (PyObject_TypeCheck(obj, &_ExprType)) {
    ExprObject *e = (ExprObject *)obj;
    if (e->ctx_obj != ctx_obj) {
      PyErr_SetString(
          PyExc_ValueError,
          "ixsimpl: cannot mix expressions from different contexts");
      return NULL;
    }
    return e->node;
  }
  if (PyLong_Check(obj)) {
    int overflow = 0;
    long long v = PyLong_AsLongLongAndOverflow(obj, &overflow);
    if (overflow || v < INT64_MIN || v > INT64_MAX) {
      PyErr_SetString(PyExc_OverflowError, "integer too large for ixsimpl");
      return NULL;
    }
    if (v == -1 && PyErr_Occurred())
      return NULL;
    return ixs_int(Context_session(ctx_obj), (int64_t)v);
  }
  PyErr_SetString(PyExc_TypeError, "ixsimpl: expected Expr or int");
  return NULL;
}

/* Helper: extract ctx from either operand in a binary op. */
static ContextObject *binop_ctx(PyObject *a, PyObject *b) {
  if (PyObject_TypeCheck(a, &_ExprType))
    return ((ExprObject *)a)->ctx_obj;
  if (PyObject_TypeCheck(b, &_ExprType))
    return ((ExprObject *)b)->ctx_obj;
  return NULL;
}

/* --- repr / str --- */

static PyObject *print_to_pystr(ixs_node *node,
                                size_t (*fn)(ixs_node *, char *, size_t)) {
  char stack_buf[8192];
  size_t n = fn(node, stack_buf, sizeof(stack_buf));
  if (n < sizeof(stack_buf))
    return PyUnicode_FromStringAndSize(stack_buf, (Py_ssize_t)n);
  char *heap = PyMem_Malloc(n + 1);
  if (!heap)
    return PyErr_NoMemory();
  fn(node, heap, n + 1);
  PyObject *result = PyUnicode_FromStringAndSize(heap, (Py_ssize_t)n);
  PyMem_Free(heap);
  return result;
}

static PyObject *Expr_repr(ExprObject *self) {
  if (ixs_is_error(self->node))
    return PyUnicode_FromString("<error>");
  return print_to_pystr(self->node, ixs_print);
}

static PyObject *Expr_str(ExprObject *self) { return Expr_repr(self); }

/* --- __int__ --- */

static PyObject *Expr_int(ExprObject *self) {
  if (ixs_node_tag(self->node) != IXS_INT) {
    PyErr_SetString(PyExc_TypeError,
                    "ixsimpl: only integer nodes can be converted to int");
    return NULL;
  }
  return PyLong_FromLongLong((long long)ixs_node_int_val(self->node));
}

/* --- __hash__ --- */

static Py_hash_t Expr_hash(ExprObject *self) {
  Py_hash_t h = (Py_hash_t)ixs_node_hash(self->node);
  return h == -1 ? -2 : h;
}

/* --- __eq__ / __ne__ (Python bool, pointer comparison) --- */
/* __ge__/__gt__/__le__/__lt__ return Expr (CMP nodes) for assumptions */

static PyObject *Expr_richcompare(ExprObject *self, PyObject *other, int op) {
  ContextObject *ctx_obj = self->ctx_obj;
  ixs_node *a = self->node;
  ixs_node *b;
  ixs_cmp_op cmp;
  ixs_node *result;

  if (op == Py_EQ) {
    if (PyObject_TypeCheck(other, &_ExprType)) {
      if (((ExprObject *)other)->node == self->node)
        Py_RETURN_TRUE;
      Py_RETURN_FALSE;
    }
    Py_RETURN_NOTIMPLEMENTED;
  }
  if (op == Py_NE) {
    if (PyObject_TypeCheck(other, &_ExprType)) {
      if (((ExprObject *)other)->node != self->node)
        Py_RETURN_TRUE;
      Py_RETURN_FALSE;
    }
    Py_RETURN_NOTIMPLEMENTED;
  }

  b = coerce_arg(ctx_obj, other);
  if (!b)
    return NULL;

  switch (op) {
  case Py_GE:
    cmp = IXS_CMP_GE;
    break;
  case Py_GT:
    cmp = IXS_CMP_GT;
    break;
  case Py_LE:
    cmp = IXS_CMP_LE;
    break;
  case Py_LT:
    cmp = IXS_CMP_LT;
    break;
  default:
    Py_RETURN_NOTIMPLEMENTED;
  }

  result = ixs_cmp(Context_session(ctx_obj), a, cmp, b);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

/* --- __bool__: raise TypeError for symbolic expressions --- */

static int Expr_bool(ExprObject *self) {
  ixs_tag tag = ixs_node_tag(self->node);
  if (tag == IXS_TRUE)
    return 1;
  if (tag == IXS_FALSE)
    return 0;
  PyErr_SetString(PyExc_TypeError,
                  "cannot determine truth value of symbolic expression; "
                  "use .simplify() or ixsimpl.same_node()");
  return -1;
}

/* --- Number protocol --- */

static PyObject *Expr_add(PyObject *a, PyObject *b) {
  ContextObject *ctx_obj = binop_ctx(a, b);
  ixs_node *na, *nb, *result;
  if (!ctx_obj)
    Py_RETURN_NOTIMPLEMENTED;
  na = coerce_arg(ctx_obj, a);
  if (!na)
    return NULL;
  nb = coerce_arg(ctx_obj, b);
  if (!nb)
    return NULL;
  result = ixs_add(Context_session(ctx_obj), na, nb);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *Expr_sub(PyObject *a, PyObject *b) {
  ContextObject *ctx_obj = binop_ctx(a, b);
  ixs_node *na, *nb, *result;
  if (!ctx_obj)
    Py_RETURN_NOTIMPLEMENTED;
  na = coerce_arg(ctx_obj, a);
  if (!na)
    return NULL;
  nb = coerce_arg(ctx_obj, b);
  if (!nb)
    return NULL;
  result = ixs_sub(Context_session(ctx_obj), na, nb);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *Expr_mul(PyObject *a, PyObject *b) {
  ContextObject *ctx_obj = binop_ctx(a, b);
  ixs_node *na, *nb, *result;
  if (!ctx_obj)
    Py_RETURN_NOTIMPLEMENTED;
  na = coerce_arg(ctx_obj, a);
  if (!na)
    return NULL;
  nb = coerce_arg(ctx_obj, b);
  if (!nb)
    return NULL;
  result = ixs_mul(Context_session(ctx_obj), na, nb);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *Expr_truediv(PyObject *a, PyObject *b) {
  ContextObject *ctx_obj = binop_ctx(a, b);
  ixs_node *na, *nb, *result;
  if (!ctx_obj)
    Py_RETURN_NOTIMPLEMENTED;
  na = coerce_arg(ctx_obj, a);
  if (!na)
    return NULL;
  nb = coerce_arg(ctx_obj, b);
  if (!nb)
    return NULL;
  result = ixs_div(Context_session(ctx_obj), na, nb);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *Expr_neg(ExprObject *self) {
  ixs_node *result = ixs_neg(Context_session(self->ctx_obj), self->node);
  return (PyObject *)Expr_wrap(self->ctx_obj, result);
}

static PyNumberMethods Expr_as_number = {
    .nb_add = Expr_add,
    .nb_subtract = Expr_sub,
    .nb_multiply = Expr_mul,
    .nb_negative = (unaryfunc)Expr_neg,
    .nb_bool = (inquiry)Expr_bool,
    .nb_int = (unaryfunc)Expr_int,
    .nb_true_divide = Expr_truediv,
};

/* --- Expr methods --- */

static PyObject *Expr_simplify(ExprObject *self, PyObject *args,
                               PyObject *kwargs) {
  static char *kwlist[] = {"assumptions", NULL};
  PyObject *assumptions_obj = NULL;
  ixs_node **assumptions = NULL;
  size_t n_assumptions = 0;
  ixs_node *result;
  Py_ssize_t i, n;

  if (!PyArg_ParseTupleAndKeywords(args, kwargs, "|O", kwlist,
                                   &assumptions_obj))
    return NULL;

  if (assumptions_obj && assumptions_obj != Py_None) {
    if (!PyList_Check(assumptions_obj) && !PyTuple_Check(assumptions_obj)) {
      PyErr_SetString(PyExc_TypeError,
                      "assumptions must be a list or tuple of Expr");
      return NULL;
    }
    n = PySequence_Size(assumptions_obj);
    if (n < 0)
      return NULL;
    if (n > 0) {
      assumptions = PyMem_Malloc((size_t)n * sizeof(ixs_node *));
      if (!assumptions)
        return PyErr_NoMemory();
      for (i = 0; i < n; i++) {
        PyObject *item = PySequence_GetItem(assumptions_obj, i);
        if (!item || !PyObject_TypeCheck(item, &_ExprType)) {
          Py_XDECREF(item);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_TypeError, "each assumption must be an Expr");
          return NULL;
        }
        if (((ExprObject *)item)->ctx_obj != self->ctx_obj) {
          Py_DECREF(item);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_ValueError,
                          "ixsimpl: assumption from different context");
          return NULL;
        }
        assumptions[i] = ((ExprObject *)item)->node;
        Py_DECREF(item);
      }
      n_assumptions = (size_t)n;
    }
  }

  result = ixs_simplify(Context_session(self->ctx_obj), self->node, assumptions,
                        n_assumptions);
  PyMem_Free(assumptions);
  return (PyObject *)Expr_wrap(self->ctx_obj, result);
}

static PyObject *Expr_expand(ExprObject *self, PyObject *Py_UNUSED(args)) {
  ixs_node *result = ixs_expand(Context_session(self->ctx_obj), self->node);
  return (PyObject *)Expr_wrap(self->ctx_obj, result);
}

static PyObject *Expr_to_c(ExprObject *self, PyObject *Py_UNUSED(args)) {
  if (ixs_is_error(self->node))
    return PyUnicode_FromString("/* error */");
  return print_to_pystr(self->node, ixs_print_c);
}

/* Coerce a subs key (str or Expr) to ixs_node. */
static ixs_node *coerce_subs_target(ContextObject *ctx_obj, PyObject *obj) {
  if (PyUnicode_Check(obj)) {
    const char *name = PyUnicode_AsUTF8(obj);
    if (!name)
      return NULL;
    return ixs_sym(Context_session(ctx_obj), name);
  }
  return coerce_arg(ctx_obj, obj);
}

static PyObject *Expr_subs(ExprObject *self, PyObject *args) {
  Py_ssize_t nargs = PyTuple_GET_SIZE(args);

  /* Dict form: expr.subs({target: repl, ...}) */
  if (nargs == 1 && PyDict_Check(PyTuple_GET_ITEM(args, 0))) {
    PyObject *dict = PyTuple_GET_ITEM(args, 0);
    Py_ssize_t n = PyDict_Size(dict);
    ixs_node **targets, **repls;
    ixs_node *result;
    Py_ssize_t pos = 0;
    PyObject *key, *val;
    uint32_t i = 0;

    if (n == 0)
      return (PyObject *)Expr_wrap(self->ctx_obj, self->node);

    targets = (ixs_node **)PyMem_Malloc((size_t)n * sizeof(ixs_node *));
    repls = (ixs_node **)PyMem_Malloc((size_t)n * sizeof(ixs_node *));
    if (!targets || !repls) {
      PyMem_Free(targets);
      PyMem_Free(repls);
      return PyErr_NoMemory();
    }

    while (PyDict_Next(dict, &pos, &key, &val)) {
      targets[i] = coerce_subs_target(self->ctx_obj, key);
      if (!targets[i]) {
        PyMem_Free(targets);
        PyMem_Free(repls);
        return NULL;
      }
      repls[i] = coerce_arg(self->ctx_obj, val);
      if (!repls[i]) {
        PyMem_Free(targets);
        PyMem_Free(repls);
        return NULL;
      }
      i++;
    }
    if (i != (uint32_t)n) {
      PyMem_Free(targets);
      PyMem_Free(repls);
      PyErr_SetString(PyExc_RuntimeError, "dict changed size during iteration");
      return NULL;
    }

    result = ixs_subs_multi(Context_session(self->ctx_obj), self->node,
                            (uint32_t)n, targets, repls);
    PyMem_Free(targets);
    PyMem_Free(repls);
    return (PyObject *)Expr_wrap(self->ctx_obj, result);
  }

  /* Pair form: expr.subs(target, replacement) */
  {
    PyObject *target_obj, *repl_obj;
    ixs_node *target, *repl, *result;

    if (!PyArg_ParseTuple(args, "OO", &target_obj, &repl_obj))
      return NULL;

    target = coerce_subs_target(self->ctx_obj, target_obj);
    if (!target)
      return NULL;

    repl = coerce_arg(self->ctx_obj, repl_obj);
    if (!repl)
      return NULL;

    result = ixs_subs(Context_session(self->ctx_obj), self->node, target, repl);
    return (PyObject *)Expr_wrap(self->ctx_obj, result);
  }
}

static PyObject *Expr_child(ExprObject *self, PyObject *args) {
  unsigned int i;
  uint32_t n;
  ixs_node *ch;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  n = ixs_node_nchildren(self->node);
  if (i >= n) {
    PyErr_Format(PyExc_IndexError, "child index %u out of range (nchildren=%u)",
                 i, n);
    return NULL;
  }
  ch = ixs_node_child(self->node, (uint32_t)i);
  return (PyObject *)Expr_wrap(self->ctx_obj, ch);
}

/* --- ADD accessors --- */

static PyObject *Expr_get_add_coeff(ExprObject *self,
                                    void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_ADD) {
    PyErr_SetString(PyExc_TypeError, "add_coeff requires ADD node");
    return NULL;
  }
  return (PyObject *)Expr_wrap(self->ctx_obj, ixs_node_add_coeff(self->node));
}

static PyObject *Expr_get_add_nterms(ExprObject *self,
                                     void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_ADD) {
    PyErr_SetString(PyExc_TypeError, "add_nterms requires ADD node");
    return NULL;
  }
  return PyLong_FromUnsignedLong(ixs_node_add_nterms(self->node));
}

static PyObject *Expr_add_term(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_ADD) {
    PyErr_SetString(PyExc_TypeError, "add_term requires ADD node");
    return NULL;
  }
  if (i >= ixs_node_add_nterms(self->node)) {
    PyErr_Format(PyExc_IndexError, "term index %u out of range (nterms=%u)", i,
                 ixs_node_add_nterms(self->node));
    return NULL;
  }
  return (PyObject *)Expr_wrap(self->ctx_obj,
                               ixs_node_add_term(self->node, (uint32_t)i));
}

static PyObject *Expr_add_term_coeff(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_ADD) {
    PyErr_SetString(PyExc_TypeError, "add_term_coeff requires ADD node");
    return NULL;
  }
  if (i >= ixs_node_add_nterms(self->node)) {
    PyErr_Format(PyExc_IndexError, "term index %u out of range (nterms=%u)", i,
                 ixs_node_add_nterms(self->node));
    return NULL;
  }
  return (PyObject *)Expr_wrap(
      self->ctx_obj, ixs_node_add_term_coeff(self->node, (uint32_t)i));
}

/* --- MUL accessors --- */

static PyObject *Expr_get_mul_coeff(ExprObject *self,
                                    void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_MUL) {
    PyErr_SetString(PyExc_TypeError, "mul_coeff requires MUL node");
    return NULL;
  }
  return (PyObject *)Expr_wrap(self->ctx_obj, ixs_node_mul_coeff(self->node));
}

static PyObject *Expr_mul_factor_base(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_MUL) {
    PyErr_SetString(PyExc_TypeError, "mul_factor_base requires MUL node");
    return NULL;
  }
  if (i >= ixs_node_mul_nfactors(self->node)) {
    PyErr_Format(PyExc_IndexError, "factor index %u out of range (nfactors=%u)",
                 i, ixs_node_mul_nfactors(self->node));
    return NULL;
  }
  return (PyObject *)Expr_wrap(
      self->ctx_obj, ixs_node_mul_factor_base(self->node, (uint32_t)i));
}

/* --- PW accessors --- */

static PyObject *Expr_get_pw_ncases(ExprObject *self,
                                    void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_PIECEWISE) {
    PyErr_SetString(PyExc_TypeError, "pw_ncases requires PIECEWISE node");
    return NULL;
  }
  return PyLong_FromUnsignedLong(ixs_node_pw_ncases(self->node));
}

static PyObject *Expr_pw_value(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_PIECEWISE) {
    PyErr_SetString(PyExc_TypeError, "pw_value requires PIECEWISE node");
    return NULL;
  }
  if (i >= ixs_node_pw_ncases(self->node)) {
    PyErr_Format(PyExc_IndexError, "case index %u out of range (ncases=%u)", i,
                 ixs_node_pw_ncases(self->node));
    return NULL;
  }
  return (PyObject *)Expr_wrap(self->ctx_obj,
                               ixs_node_pw_value(self->node, (uint32_t)i));
}

static PyObject *Expr_pw_cond(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_PIECEWISE) {
    PyErr_SetString(PyExc_TypeError, "pw_cond requires PIECEWISE node");
    return NULL;
  }
  if (i >= ixs_node_pw_ncases(self->node)) {
    PyErr_Format(PyExc_IndexError, "case index %u out of range (ncases=%u)", i,
                 ixs_node_pw_ncases(self->node));
    return NULL;
  }
  return (PyObject *)Expr_wrap(self->ctx_obj,
                               ixs_node_pw_cond(self->node, (uint32_t)i));
}

static PyObject *Expr_mul_factor_exp(ExprObject *self, PyObject *args) {
  unsigned int i;
  if (!PyArg_ParseTuple(args, "I", &i))
    return NULL;
  if (ixs_node_tag(self->node) != IXS_MUL) {
    PyErr_SetString(PyExc_TypeError, "mul_factor_exp requires MUL node");
    return NULL;
  }
  if (i >= ixs_node_mul_nfactors(self->node)) {
    PyErr_Format(PyExc_IndexError, "factor index %u out of range (nfactors=%u)",
                 i, ixs_node_mul_nfactors(self->node));
    return NULL;
  }
  return PyLong_FromLong(ixs_node_mul_factor_exp(self->node, (uint32_t)i));
}

static PyMethodDef Expr_methods[] = {
    {"simplify", (PyCFunction)Expr_simplify, METH_VARARGS | METH_KEYWORDS,
     "Simplify expression with optional assumptions."},
    {"expand", (PyCFunction)Expr_expand, METH_NOARGS,
     "Distribute MUL over ADD (expand products of sums)."},
    {"to_c", (PyCFunction)Expr_to_c, METH_NOARGS,
     "Return C code representation."},
    {"subs", (PyCFunction)Expr_subs, METH_VARARGS,
     "expr.subs(target, repl) or expr.subs({t1: r1, ...}): simultaneous "
     "substitution. Keys can be str or Expr; values can be Expr or int."},
    {"child", (PyCFunction)Expr_child, METH_VARARGS,
     "expr.child(i) -> Expr: i-th child node (0 <= i < nchildren)."},
    {"add_term", (PyCFunction)Expr_add_term, METH_VARARGS,
     "expr.add_term(i) -> Expr: i-th term (ADD only)."},
    {"add_term_coeff", (PyCFunction)Expr_add_term_coeff, METH_VARARGS,
     "expr.add_term_coeff(i) -> Expr: coefficient of i-th term (ADD only)."},
    {"mul_factor_base", (PyCFunction)Expr_mul_factor_base, METH_VARARGS,
     "expr.mul_factor_base(i) -> Expr: base of i-th factor (MUL only)."},
    {"mul_factor_exp", (PyCFunction)Expr_mul_factor_exp, METH_VARARGS,
     "expr.mul_factor_exp(i) -> int: exponent of i-th factor (MUL only)."},
    {"pw_value", (PyCFunction)Expr_pw_value, METH_VARARGS,
     "expr.pw_value(i) -> Expr: value of i-th case (PIECEWISE only)."},
    {"pw_cond", (PyCFunction)Expr_pw_cond, METH_VARARGS,
     "expr.pw_cond(i) -> Expr: condition of i-th case (PIECEWISE only)."},
    {NULL}};

/* --- Expr properties --- */

static PyObject *Expr_get_is_error(ExprObject *self, void *Py_UNUSED(closure)) {
  return PyBool_FromLong(ixs_is_error(self->node));
}

static PyObject *Expr_get_is_parse_error(ExprObject *self,
                                         void *Py_UNUSED(closure)) {
  return PyBool_FromLong(ixs_is_parse_error(self->node));
}

static PyObject *Expr_get_is_domain_error(ExprObject *self,
                                          void *Py_UNUSED(closure)) {
  return PyBool_FromLong(ixs_is_domain_error(self->node));
}

static PyObject *Expr_get_is_expr(ExprObject *self, void *Py_UNUSED(closure)) {
  return PyBool_FromLong(ixs_node_is_expr(self->node));
}

static PyObject *Expr_get_is_pred(ExprObject *self, void *Py_UNUSED(closure)) {
  return PyBool_FromLong(ixs_node_is_pred(self->node));
}

static PyObject *Expr_get_tag(ExprObject *self, void *Py_UNUSED(closure)) {
  return PyLong_FromLong((long)ixs_node_tag(self->node));
}

static PyObject *Expr_get_nchildren(ExprObject *self,
                                    void *Py_UNUSED(closure)) {
  return PyLong_FromUnsignedLong(ixs_node_nchildren(self->node));
}

static PyObject *Expr_get_children(ExprObject *self, void *Py_UNUSED(closure)) {
  uint32_t n = ixs_node_nchildren(self->node);
  uint32_t i;
  PyObject *tup = PyTuple_New((Py_ssize_t)n);
  if (!tup)
    return NULL;
  for (i = 0; i < n; i++) {
    ExprObject *child = Expr_wrap(self->ctx_obj, ixs_node_child(self->node, i));
    if (!child) {
      Py_DECREF(tup);
      return NULL;
    }
    PyTuple_SET_ITEM(tup, (Py_ssize_t)i, (PyObject *)child);
  }
  return tup;
}

static PyObject *Expr_get_sym_name(ExprObject *self, void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_SYM) {
    PyErr_SetString(PyExc_TypeError, "sym_name requires SYM node");
    return NULL;
  }
  return PyUnicode_FromString(ixs_node_sym_name(self->node));
}

static PyObject *Expr_get_rat_num(ExprObject *self, void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_RAT) {
    PyErr_SetString(PyExc_TypeError, "rat_num requires RAT node");
    return NULL;
  }
  return PyLong_FromLongLong(ixs_node_rat_num(self->node));
}

static PyObject *Expr_get_rat_den(ExprObject *self, void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_RAT) {
    PyErr_SetString(PyExc_TypeError, "rat_den requires RAT node");
    return NULL;
  }
  return PyLong_FromLongLong(ixs_node_rat_den(self->node));
}

static PyObject *Expr_get_mul_nfactors(ExprObject *self,
                                       void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_MUL) {
    PyErr_SetString(PyExc_TypeError, "mul_nfactors requires MUL node");
    return NULL;
  }
  return PyLong_FromUnsignedLong(ixs_node_mul_nfactors(self->node));
}

static PyObject *Expr_get_ctx(ExprObject *self, void *Py_UNUSED(closure)) {
  Py_INCREF(self->ctx_obj);
  return (PyObject *)self->ctx_obj;
}

static PyObject *Expr_get_cmp_op(ExprObject *self, void *Py_UNUSED(closure)) {
  if (ixs_node_tag(self->node) != IXS_CMP) {
    PyErr_SetString(PyExc_TypeError, "cmp_op requires CMP node");
    return NULL;
  }
  return PyLong_FromLong((long)ixs_node_cmp_op(self->node));
}

static PyGetSetDef Expr_getset[] = {
    {"is_error", (getter)Expr_get_is_error, NULL,
     "True if node is any error sentinel.", NULL},
    {"is_parse_error", (getter)Expr_get_is_parse_error, NULL,
     "True if node is a parse error sentinel.", NULL},
    {"is_domain_error", (getter)Expr_get_is_domain_error, NULL,
     "True if node is a domain error sentinel.", NULL},
    {"is_expr", (getter)Expr_get_is_expr, NULL,
     "True if node is an expression root.", NULL},
    {"is_pred", (getter)Expr_get_is_pred, NULL,
     "True if node is a predicate root.", NULL},
    {"tag", (getter)Expr_get_tag, NULL, "Node type tag (ixs_tag enum).", NULL},
    {"nchildren", (getter)Expr_get_nchildren, NULL,
     "Number of child node pointers (0 for leaves).", NULL},
    {"children", (getter)Expr_get_children, NULL, "Tuple of child Expr nodes.",
     NULL},
    {"sym_name", (getter)Expr_get_sym_name, NULL,
     "Symbol name (str). Only valid for SYM nodes.", NULL},
    {"rat_num", (getter)Expr_get_rat_num, NULL,
     "Rational numerator (int). Only valid for RAT nodes.", NULL},
    {"rat_den", (getter)Expr_get_rat_den, NULL,
     "Rational denominator (int). Only valid for RAT nodes.", NULL},
    {"add_coeff", (getter)Expr_get_add_coeff, NULL,
     "Constant coefficient (Expr). Only valid for ADD nodes.", NULL},
    {"add_nterms", (getter)Expr_get_add_nterms, NULL,
     "Number of terms (int). Only valid for ADD nodes.", NULL},
    {"mul_coeff", (getter)Expr_get_mul_coeff, NULL,
     "Constant coefficient (Expr). Only valid for MUL nodes.", NULL},
    {"mul_nfactors", (getter)Expr_get_mul_nfactors, NULL,
     "Number of factors (int). Only valid for MUL nodes.", NULL},
    {"pw_ncases", (getter)Expr_get_pw_ncases, NULL,
     "Number of cases (int). Only valid for PIECEWISE nodes.", NULL},
    {"cmp_op", (getter)Expr_get_cmp_op, NULL,
     "Comparison operator (int, CMP_* constant). Only valid for CMP nodes.",
     NULL},
    {"_ctx", (getter)Expr_get_ctx, NULL, "Owning Context (internal).", NULL},
    {NULL}};

static PyTypeObject _ExprType = {
    .ob_base = PyVarObject_HEAD_INIT(NULL, 0).tp_name = "ixsimpl._Expr",
    .tp_basicsize = sizeof(ExprObject),
    .tp_dealloc = (destructor)Expr_dealloc,
    .tp_repr = (reprfunc)Expr_repr,
    .tp_as_number = &Expr_as_number,
    .tp_hash = (hashfunc)Expr_hash,
    .tp_str = (reprfunc)Expr_str,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,
    .tp_doc = "ixsimpl expression node (internal base type).",
    .tp_richcompare = (richcmpfunc)Expr_richcompare,
    .tp_methods = Expr_methods,
    .tp_getset = Expr_getset,
};

/* ------------------------------------------------------------------ */
/*  Context methods and type                                          */
/* ------------------------------------------------------------------ */

static PyObject *Context_new(PyTypeObject *type, PyObject *Py_UNUSED(args),
                             PyObject *Py_UNUSED(kwargs)) {
  ContextObject *self = (ContextObject *)type->tp_alloc(type, 0);
  if (!self)
    return NULL;
  self->ctx = NULL;
  self->ctx = ixs_ctx_create();
  if (!self->ctx) {
    Py_DECREF(self);
    PyErr_SetString(PyExc_MemoryError, "ixsimpl: failed to create context");
    return NULL;
  }
  ixs_session_init(&self->session, self->ctx);
  return (PyObject *)self;
}

static void Context_dealloc(ContextObject *self) {
  if (self->ctx) {
    ixs_session_destroy(&self->session);
    ixs_ctx_destroy(self->ctx);
  }
  Py_TYPE(self)->tp_free((PyObject *)self);
}

/* --- Context methods --- */

static PyObject *Context_sym(ContextObject *self, PyObject *args) {
  const char *name;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "s", &name))
    return NULL;
  node = ixs_sym(Context_session(self), name);
  return (PyObject *)Expr_wrap(self, node);
}

typedef ixs_node *(*Context_parse_fn)(ixs_session *, const char *, size_t);

static PyObject *Context_parse_with(ContextObject *self, PyObject *args,
                                    Context_parse_fn parse_fn) {
  const char *input;
  Py_ssize_t len;
  ixs_node *node;

  if (!PyArg_ParseTuple(args, "s#", &input, &len))
    return NULL;
  node = parse_fn(Context_session(self), input, (size_t)len);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_parse(ContextObject *self, PyObject *args) {
  return Context_parse_with(self, args, ixs_parse);
}

static PyObject *Context_parse_expr(ContextObject *self, PyObject *args) {
  return Context_parse_with(self, args, ixs_parse_expr);
}

static PyObject *Context_parse_pred(ContextObject *self, PyObject *args) {
  return Context_parse_with(self, args, ixs_parse_pred);
}

static PyObject *Context_int_(ContextObject *self, PyObject *args) {
  long long val;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "L", &val))
    return NULL;
  node = ixs_int(Context_session(self), (int64_t)val);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_rat(ContextObject *self, PyObject *args) {
  long long p, q;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "LL", &p, &q))
    return NULL;
  node = ixs_rat(Context_session(self), (int64_t)p, (int64_t)q);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_true_(ContextObject *self, PyObject *Py_UNUSED(args)) {
  return (PyObject *)Expr_wrap(self, ixs_true(Context_session(self)));
}

static PyObject *Context_false_(ContextObject *self,
                                PyObject *Py_UNUSED(args)) {
  return (PyObject *)Expr_wrap(self, ixs_false(Context_session(self)));
}

static PyObject *Context_import_(ContextObject *self, PyObject *arg) {
  ExprObject *expr;
  ixs_node *node;

  if (!PyObject_TypeCheck(arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "expr must be an Expr");
    return NULL;
  }

  expr = (ExprObject *)arg;
  node = ixs_import_node(Context_session(self), expr->node);
  if (!node)
    return PyErr_NoMemory();
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_serialize(ContextObject *self, PyObject *arg) {
  ExprObject *expr;
  ixs_session *session;
  size_t before_nerrors;
  size_t after_nerrors;
  PyObject *tmp;
  PyObject *result;
  BytesWriterState state;
  ixs_writer writer;

  if (!PyObject_TypeCheck(arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "expr must be an Expr");
    return NULL;
  }

  expr = (ExprObject *)arg;
  session = Context_session(self);
  before_nerrors = ixs_session_nerrors(session);
  tmp = PyByteArray_FromStringAndSize(NULL, 0);
  if (!tmp)
    return NULL;

  state.buf_obj = tmp;
  writer.write = BytesWriter_write;
  writer.userdata = &state;
  if (!ixs_serialize_node(session, expr->node, &writer)) {
    after_nerrors = ixs_session_nerrors(session);
    Py_DECREF(tmp);
    if (PyErr_Occurred())
      return NULL;
    if (after_nerrors > before_nerrors) {
      PyErr_SetString(PyExc_RuntimeError,
                      ixs_session_error(session, before_nerrors));
      return NULL;
    }
    return PyErr_NoMemory();
  }

  result = PyBytes_FromStringAndSize(PyByteArray_AS_STRING(tmp),
                                     PyByteArray_GET_SIZE(tmp));
  Py_DECREF(tmp);
  return result;
}

static PyObject *Context_deserialize(ContextObject *self, PyObject *arg) {
  Py_buffer view;
  BytesReaderState state;
  ixs_reader reader;
  ixs_node *node;

  if (PyObject_GetBuffer(arg, &view, PyBUF_CONTIG_RO) < 0)
    return NULL;

  state.data = (const unsigned char *)view.buf;
  state.len = view.len;
  state.pos = 0;
  reader.read = BytesReader_read;
  reader.remaining = BytesReader_remaining;
  reader.userdata = &state;
  node = ixs_deserialize_node(Context_session(self), &reader);
  PyBuffer_Release(&view);
  if (!node)
    return PyErr_NoMemory();
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_eq(ContextObject *self, PyObject *args) {
  PyObject *a_obj, *b_obj;
  ixs_node *a, *b, *result;
  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;
  a = coerce_arg(self, a_obj);
  if (!a)
    return NULL;
  b = coerce_arg(self, b_obj);
  if (!b)
    return NULL;
  result = ixs_cmp(Context_session(self), a, IXS_CMP_EQ, b);
  return (PyObject *)Expr_wrap(self, result);
}

static PyObject *Context_ne(ContextObject *self, PyObject *args) {
  PyObject *a_obj, *b_obj;
  ixs_node *a, *b, *result;
  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;
  a = coerce_arg(self, a_obj);
  if (!a)
    return NULL;
  b = coerce_arg(self, b_obj);
  if (!b)
    return NULL;
  result = ixs_cmp(Context_session(self), a, IXS_CMP_NE, b);
  return (PyObject *)Expr_wrap(self, result);
}

static PyObject *Context_check(ContextObject *self, PyObject *args,
                               PyObject *kwargs) {
  static char *kwlist[] = {"expr", "assumptions", NULL};
  PyObject *expr_obj, *assumptions_obj = NULL;
  Py_ssize_t i, n_assumptions = 0;
  ixs_node *expr, **assumptions = NULL;
  ixs_check_result r;

  if (!PyArg_ParseTupleAndKeywords(args, kwargs, "O|O", kwlist, &expr_obj,
                                   &assumptions_obj))
    return NULL;

  if (!PyObject_TypeCheck(expr_obj, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "expr must be an Expr");
    return NULL;
  }
  if (((ExprObject *)expr_obj)->ctx_obj != self) {
    PyErr_SetString(PyExc_ValueError,
                    "ixsimpl: expression from different context");
    return NULL;
  }
  expr = ((ExprObject *)expr_obj)->node;

  if (assumptions_obj && assumptions_obj != Py_None) {
    n_assumptions = PySequence_Size(assumptions_obj);
    if (n_assumptions < 0)
      return NULL;
    if (n_assumptions > 0) {
      assumptions = PyMem_Malloc((size_t)n_assumptions * sizeof(ixs_node *));
      if (!assumptions)
        return PyErr_NoMemory();
      for (i = 0; i < n_assumptions; i++) {
        PyObject *item = PySequence_GetItem(assumptions_obj, i);
        if (!item || !PyObject_TypeCheck(item, &_ExprType)) {
          Py_XDECREF(item);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_TypeError, "each assumption must be an Expr");
          return NULL;
        }
        if (((ExprObject *)item)->ctx_obj != self) {
          Py_DECREF(item);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_ValueError,
                          "ixsimpl: assumption from different context");
          return NULL;
        }
        assumptions[i] = ((ExprObject *)item)->node;
        Py_DECREF(item);
      }
    }
  }

  r = ixs_check(Context_session(self), expr, assumptions,
                (size_t)n_assumptions);
  PyMem_Free(assumptions);

  if (r == IXS_CHECK_TRUE)
    Py_RETURN_TRUE;
  if (r == IXS_CHECK_FALSE)
    Py_RETURN_FALSE;
  Py_RETURN_NONE;
}

static PyObject *Context_simplify_batch(ContextObject *self, PyObject *args,
                                        PyObject *kwargs) {
  static char *kwlist[] = {"exprs", "assumptions", NULL};
  PyObject *exprs_obj, *assumptions_obj = NULL;
  Py_ssize_t i, n_exprs, n_assumptions = 0;
  ixs_node **exprs = NULL, **assumptions = NULL;

  if (!PyArg_ParseTupleAndKeywords(args, kwargs, "O|O", kwlist, &exprs_obj,
                                   &assumptions_obj))
    return NULL;

  if (!PyList_Check(exprs_obj)) {
    PyErr_SetString(PyExc_TypeError, "exprs must be a list of Expr");
    return NULL;
  }
  n_exprs = PyList_Size(exprs_obj);
  exprs = PyMem_Malloc((size_t)n_exprs * sizeof(ixs_node *));
  if (!exprs)
    return PyErr_NoMemory();

  for (i = 0; i < n_exprs; i++) {
    PyObject *item = PyList_GetItem(exprs_obj, i);
    if (!PyObject_TypeCheck(item, &_ExprType)) {
      PyMem_Free(exprs);
      PyErr_SetString(PyExc_TypeError, "each expr must be an Expr");
      return NULL;
    }
    if (((ExprObject *)item)->ctx_obj != self) {
      PyMem_Free(exprs);
      PyErr_SetString(PyExc_ValueError,
                      "ixsimpl: expression from different context");
      return NULL;
    }
    exprs[i] = ((ExprObject *)item)->node;
  }

  if (assumptions_obj && assumptions_obj != Py_None) {
    n_assumptions = PySequence_Size(assumptions_obj);
    if (n_assumptions < 0) {
      PyMem_Free(exprs);
      return NULL;
    }
    if (n_assumptions > 0) {
      assumptions = PyMem_Malloc((size_t)n_assumptions * sizeof(ixs_node *));
      if (!assumptions) {
        PyMem_Free(exprs);
        return PyErr_NoMemory();
      }
      for (i = 0; i < n_assumptions; i++) {
        PyObject *item = PySequence_GetItem(assumptions_obj, i);
        if (!item || !PyObject_TypeCheck(item, &_ExprType)) {
          Py_XDECREF(item);
          PyMem_Free(exprs);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_TypeError, "each assumption must be an Expr");
          return NULL;
        }
        if (((ExprObject *)item)->ctx_obj != self) {
          Py_DECREF(item);
          PyMem_Free(exprs);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_ValueError,
                          "ixsimpl: assumption from different context");
          return NULL;
        }
        assumptions[i] = ((ExprObject *)item)->node;
        Py_DECREF(item);
      }
    }
  }

  ixs_simplify_batch(Context_session(self), exprs, (size_t)n_exprs, assumptions,
                     (size_t)n_assumptions);

  for (i = 0; i < n_exprs; i++) {
    if (!exprs[i]) {
      PyMem_Free(exprs);
      PyMem_Free(assumptions);
      PyErr_SetString(PyExc_MemoryError, "ixsimpl: OOM during batch simplify");
      return NULL;
    }
    ExprObject *new_expr = Expr_wrap(self, exprs[i]);
    if (!new_expr) {
      PyMem_Free(exprs);
      PyMem_Free(assumptions);
      return NULL;
    }
    PyList_SetItem(exprs_obj, i, (PyObject *)new_expr);
  }

  PyMem_Free(exprs);
  PyMem_Free(assumptions);
  Py_RETURN_NONE;
}

static PyObject *Context_clear_errors(ContextObject *self,
                                      PyObject *Py_UNUSED(args)) {
  ixs_session_clear_errors(Context_session(self));
  Py_RETURN_NONE;
}

static PyObject *Context_stats(ContextObject *self, PyObject *Py_UNUSED(args)) {
  size_t n = ixs_ctx_nstats(self->ctx);
  size_t i;
  PyObject *dict = PyDict_New();
  if (!dict)
    return NULL;
  for (i = 0; i < n; i++) {
    const char *name = NULL;
    uint64_t count = ixs_ctx_stat(self->ctx, i, &name);
    if (!name)
      break;
    PyObject *key = PyUnicode_FromString(name);
    PyObject *val = PyLong_FromUnsignedLongLong(count);
    if (!key || !val || PyDict_SetItem(dict, key, val) < 0) {
      Py_XDECREF(key);
      Py_XDECREF(val);
      Py_DECREF(dict);
      return NULL;
    }
    Py_DECREF(key);
    Py_DECREF(val);
  }
  return dict;
}

static PyObject *Context_stats_reset(ContextObject *self,
                                     PyObject *Py_UNUSED(args)) {
  ixs_ctx_stats_reset(self->ctx);
  Py_RETURN_NONE;
}

static PyMethodDef Context_methods[] = {
    {"sym", (PyCFunction)Context_sym, METH_VARARGS,
     "Create a symbol: ctx.sym('x')."},
    {"parse", (PyCFunction)Context_parse, METH_VARARGS,
     "Parse a SymPy-like expression string. Alias of parse_expr()."},
    {"parse_expr", (PyCFunction)Context_parse_expr, METH_VARARGS,
     "Parse a SymPy-like expression string and reject predicate roots."},
    {"parse_pred", (PyCFunction)Context_parse_pred, METH_VARARGS,
     "Parse a predicate string and reject expression roots."},
    {"int_", (PyCFunction)Context_int_, METH_VARARGS,
     "Create an integer node: ctx.int_(42)."},
    {"rat", (PyCFunction)Context_rat, METH_VARARGS,
     "Create a rational node: ctx.rat(1, 3)."},
    {"true_", (PyCFunction)Context_true_, METH_NOARGS, "Return True node."},
    {"false_", (PyCFunction)Context_false_, METH_NOARGS, "Return False node."},
    {"import_", (PyCFunction)Context_import_, METH_O,
     "Import an Expr from another Context's store into this one."},
    {"serialize", (PyCFunction)Context_serialize, METH_O,
     "Serialize an Expr to stable little-endian bytes. Raises MemoryError on "
     "allocation failure and RuntimeError on codec validation failure."},
    {"deserialize", (PyCFunction)Context_deserialize, METH_O,
     "Deserialize stable little-endian bytes into this Context. Malformed "
     "input returns a parse-error Expr; OOM raises MemoryError."},
    {"eq", (PyCFunction)Context_eq, METH_VARARGS,
     "Build an equality CMP node: ctx.eq(a, b)."},
    {"ne", (PyCFunction)Context_ne, METH_VARARGS,
     "Build an inequality CMP node: ctx.ne(a, b)."},
    {"check", (PyCFunction)Context_check, METH_VARARGS | METH_KEYWORDS,
     "True if provable, False if contradicted, None if undecidable from "
     "bounds."},
    {"simplify_batch", (PyCFunction)Context_simplify_batch,
     METH_VARARGS | METH_KEYWORDS, "Simplify a list of Expr in-place."},
    {"clear_errors", (PyCFunction)Context_clear_errors, METH_NOARGS,
     "Clear the error list."},
    {"stats", (PyCFunction)Context_stats, METH_NOARGS,
     "Rule-hit statistics as {name: count} dict (empty if not compiled with "
     "IXS_STATS)."},
    {"stats_reset", (PyCFunction)Context_stats_reset, METH_NOARGS,
     "Reset all rule-hit counters to zero."},
    {NULL}};

/* --- Context properties --- */

static PyObject *Context_get_errors(ContextObject *self,
                                    void *Py_UNUSED(closure)) {
  size_t n = ixs_session_nerrors(Context_session(self));
  size_t i;
  PyObject *list = PyList_New((Py_ssize_t)n);
  if (!list)
    return NULL;
  for (i = 0; i < n; i++) {
    const char *msg = ixs_session_error(Context_session(self), i);
    PyObject *s = PyUnicode_FromString(msg ? msg : "");
    if (!s) {
      Py_DECREF(list);
      return NULL;
    }
    PyList_SET_ITEM(list, (Py_ssize_t)i, s);
  }
  return list;
}

static PyGetSetDef Context_getset[] = {
    {"errors", (getter)Context_get_errors, NULL,
     "List of error messages from the last operation.", NULL},
    {NULL}};

static PyTypeObject ContextType = {
    .ob_base = PyVarObject_HEAD_INIT(NULL, 0).tp_name = "ixsimpl.Context",
    .tp_basicsize = sizeof(ContextObject),
    .tp_dealloc = (destructor)Context_dealloc,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_doc =
        "ixsimpl expression context. All expressions belong to a context.",
    .tp_methods = Context_methods,
    .tp_getset = Context_getset,
    .tp_new = Context_new,
};

/* ------------------------------------------------------------------ */
/*  Module-level functions                                            */
/* ------------------------------------------------------------------ */

static PyObject *mod_floor(PyObject *Py_UNUSED(module), PyObject *arg) {
  ExprObject *e;
  ixs_node *result;
  if (!PyObject_TypeCheck(arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.floor() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_floor(Context_session(e->ctx_obj), e->node);
  return (PyObject *)Expr_wrap(e->ctx_obj, result);
}

static PyObject *mod_ceil(PyObject *Py_UNUSED(module), PyObject *arg) {
  ExprObject *e;
  ixs_node *result;
  if (!PyObject_TypeCheck(arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.ceil() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_ceil(Context_session(e->ctx_obj), e->node);
  return (PyObject *)Expr_wrap(e->ctx_obj, result);
}

static PyObject *mod_binary_op(PyObject *args,
                               ixs_node *(*op)(ixs_session *, ixs_node *,
                                               ixs_node *),
                               const char *name) {
  PyObject *a_obj, *b_obj;
  ExprObject *ae;
  ixs_node *a, *b, *result;

  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;

  if (!PyObject_TypeCheck(a_obj, &_ExprType)) {
    PyErr_Format(PyExc_TypeError, "ixsimpl.%s() first arg must be Expr", name);
    return NULL;
  }
  ae = (ExprObject *)a_obj;
  a = ae->node;
  b = coerce_arg(ae->ctx_obj, b_obj);
  if (!b)
    return NULL;

  result = op(Context_session(ae->ctx_obj), a, b);
  return (PyObject *)Expr_wrap(ae->ctx_obj, result);
}

static PyObject *mod_mod(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_mod, "mod");
}

static PyObject *mod_max_(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_max, "max_");
}

static PyObject *mod_min_(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_min, "min_");
}

static PyObject *mod_xor_(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_xor, "xor_");
}

static PyObject *mod_and_(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_and, "and_");
}

static PyObject *mod_or_(PyObject *Py_UNUSED(module), PyObject *args) {
  return mod_binary_op(args, ixs_or, "or_");
}

static PyObject *mod_not_(PyObject *Py_UNUSED(module), PyObject *arg) {
  ExprObject *e;
  ixs_node *result;
  if (!PyObject_TypeCheck(arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.not_() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_not(Context_session(e->ctx_obj), e->node);
  return (PyObject *)Expr_wrap(e->ctx_obj, result);
}

static PyObject *mod_pw(PyObject *Py_UNUSED(module), PyObject *args) {
  Py_ssize_t n = PyTuple_Size(args);
  Py_ssize_t i;
  ContextObject *ctx_obj;
  ixs_node **values, **conds;
  ixs_node *result;

  if (n < 1) {
    PyErr_SetString(PyExc_TypeError,
                    "ixsimpl.pw() requires at least one (value, cond) pair");
    return NULL;
  }
  if (n > UINT32_MAX) {
    PyErr_SetString(PyExc_OverflowError, "ixsimpl.pw() too many branches");
    return NULL;
  }

  values = PyMem_Malloc((size_t)n * sizeof(ixs_node *));
  conds = PyMem_Malloc((size_t)n * sizeof(ixs_node *));
  if (!values || !conds) {
    PyMem_Free(values);
    PyMem_Free(conds);
    return PyErr_NoMemory();
  }

  ctx_obj = NULL;
  for (i = 0; i < n; i++) {
    PyObject *pair = PyTuple_GetItem(args, i);
    PyObject *val_obj, *cond_obj;
    if (!PyTuple_Check(pair) || PyTuple_Size(pair) != 2) {
      PyMem_Free(values);
      PyMem_Free(conds);
      PyErr_SetString(PyExc_TypeError,
                      "ixsimpl.pw() each arg must be a (value, cond) tuple");
      return NULL;
    }
    val_obj = PyTuple_GetItem(pair, 0);
    cond_obj = PyTuple_GetItem(pair, 1);

    if (!ctx_obj) {
      if (PyObject_TypeCheck(val_obj, &_ExprType))
        ctx_obj = ((ExprObject *)val_obj)->ctx_obj;
      else if (PyObject_TypeCheck(cond_obj, &_ExprType))
        ctx_obj = ((ExprObject *)cond_obj)->ctx_obj;
      else {
        PyMem_Free(values);
        PyMem_Free(conds);
        PyErr_SetString(PyExc_TypeError,
                        "ixsimpl.pw() requires at least one Expr argument");
        return NULL;
      }
    }

    values[i] = coerce_arg(ctx_obj, val_obj);
    if (!values[i]) {
      PyMem_Free(values);
      PyMem_Free(conds);
      return NULL;
    }
    conds[i] = coerce_arg(ctx_obj, cond_obj);
    if (!conds[i]) {
      PyMem_Free(values);
      PyMem_Free(conds);
      return NULL;
    }
  }

  result = ixs_pw(Context_session(ctx_obj), (uint32_t)n, values, conds);
  PyMem_Free(values);
  PyMem_Free(conds);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *mod_same_node(PyObject *Py_UNUSED(module), PyObject *args) {
  PyObject *a_obj, *b_obj;
  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;
  if (!PyObject_TypeCheck(a_obj, &_ExprType) ||
      !PyObject_TypeCheck(b_obj, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError,
                    "ixsimpl.same_node() requires two Expr arguments");
    return NULL;
  }
  return PyBool_FromLong(
      ixs_same_node(((ExprObject *)a_obj)->node, ((ExprObject *)b_obj)->node));
}

static PyObject *mod_set_expr_class(PyObject *Py_UNUSED(module),
                                    PyObject *arg) {
  if (!PyType_Check(arg) ||
      !PyType_IsSubtype((PyTypeObject *)arg, &_ExprType)) {
    PyErr_SetString(PyExc_TypeError, "argument must be a subclass of _Expr");
    return NULL;
  }
  Py_INCREF(arg);
  Py_XDECREF(expr_wrap_type);
  expr_wrap_type = (PyTypeObject *)arg;
  Py_RETURN_NONE;
}

static PyMethodDef module_methods[] = {
    {"floor", (PyCFunction)mod_floor, METH_O,
     "floor(expr) -> Expr: apply floor function."},
    {"ceil", (PyCFunction)mod_ceil, METH_O,
     "ceil(expr) -> Expr: apply ceiling function."},
    {"mod", (PyCFunction)mod_mod, METH_VARARGS,
     "mod(a, b) -> Expr: floored modulo."},
    {"max_", (PyCFunction)mod_max_, METH_VARARGS,
     "max_(a, b) -> Expr: maximum."},
    {"min_", (PyCFunction)mod_min_, METH_VARARGS,
     "min_(a, b) -> Expr: minimum."},
    {"xor_", (PyCFunction)mod_xor_, METH_VARARGS,
     "xor_(a, b) -> Expr: bitwise xor."},
    {"and_", (PyCFunction)mod_and_, METH_VARARGS,
     "and_(a, b) -> Expr: logical and."},
    {"or_", (PyCFunction)mod_or_, METH_VARARGS,
     "or_(a, b) -> Expr: logical or."},
    {"not_", (PyCFunction)mod_not_, METH_O, "not_(a) -> Expr: logical not."},
    {"pw", (PyCFunction)mod_pw, METH_VARARGS,
     "pw((val, cond), ...) -> Expr: piecewise expression. "
     "Each arg is a (value, condition) tuple; last condition should be true."},
    {"same_node", (PyCFunction)mod_same_node, METH_VARARGS,
     "same_node(a, b) -> bool: True if a and b are the same node (pointer "
     "eq)."},
    {"_set_expr_class", (PyCFunction)mod_set_expr_class, METH_O,
     "Register a Python subclass of _Expr as the type instantiated by all "
     "expression-returning operations."},
    {NULL}};

/* ------------------------------------------------------------------ */
/*  Module init                                                       */
/* ------------------------------------------------------------------ */

static struct PyModuleDef ixsimpl_module = {
    .m_base = PyModuleDef_HEAD_INIT,
    .m_name = "ixsimpl._ixsimpl",
    .m_doc = "Index expression simplifier - fast symbolic integer arithmetic.",
    .m_size = -1,
    .m_methods = module_methods,
};

PyMODINIT_FUNC PyInit__ixsimpl(void) {
  PyObject *m;

  if (PyType_Ready(&ContextType) < 0)
    return NULL;
  if (PyType_Ready(&_ExprType) < 0)
    return NULL;

  expr_wrap_type = &_ExprType;
  Py_INCREF(&_ExprType);

  m = PyModule_Create(&ixsimpl_module);
  if (!m)
    goto fail_wrap;

  Py_INCREF(&ContextType);
  if (PyModule_AddObject(m, "Context", (PyObject *)&ContextType) < 0) {
    Py_DECREF(&ContextType);
    goto fail_module;
  }

  Py_INCREF(&_ExprType);
  if (PyModule_AddObject(m, "_Expr", (PyObject *)&_ExprType) < 0) {
    Py_DECREF(&_ExprType);
    goto fail_module;
  }

  /* Export tag constants */
  PyModule_AddIntConstant(m, "INT", IXS_INT);
  PyModule_AddIntConstant(m, "RAT", IXS_RAT);
  PyModule_AddIntConstant(m, "SYM", IXS_SYM);
  PyModule_AddIntConstant(m, "ADD", IXS_ADD);
  PyModule_AddIntConstant(m, "MUL", IXS_MUL);
  PyModule_AddIntConstant(m, "FLOOR", IXS_FLOOR);
  PyModule_AddIntConstant(m, "CEIL", IXS_CEIL);
  PyModule_AddIntConstant(m, "MOD", IXS_MOD);
  PyModule_AddIntConstant(m, "PIECEWISE", IXS_PIECEWISE);
  PyModule_AddIntConstant(m, "MAX", IXS_MAX);
  PyModule_AddIntConstant(m, "MIN", IXS_MIN);
  PyModule_AddIntConstant(m, "XOR", IXS_XOR);
  PyModule_AddIntConstant(m, "CMP", IXS_CMP);
  PyModule_AddIntConstant(m, "AND", IXS_AND);
  PyModule_AddIntConstant(m, "OR", IXS_OR);
  PyModule_AddIntConstant(m, "NOT", IXS_NOT);
  PyModule_AddIntConstant(m, "TRUE", IXS_TRUE);
  PyModule_AddIntConstant(m, "FALSE", IXS_FALSE);
  PyModule_AddIntConstant(m, "ERROR", IXS_ERROR);
  PyModule_AddIntConstant(m, "PARSE_ERROR", IXS_PARSE_ERROR);

  PyModule_AddIntConstant(m, "CMP_GT", IXS_CMP_GT);
  PyModule_AddIntConstant(m, "CMP_GE", IXS_CMP_GE);
  PyModule_AddIntConstant(m, "CMP_LT", IXS_CMP_LT);
  PyModule_AddIntConstant(m, "CMP_LE", IXS_CMP_LE);
  PyModule_AddIntConstant(m, "CMP_EQ", IXS_CMP_EQ);
  PyModule_AddIntConstant(m, "CMP_NE", IXS_CMP_NE);

  return m;

fail_module:
  Py_DECREF(m);
fail_wrap:
  Py_DECREF(expr_wrap_type);
  expr_wrap_type = NULL;
  return NULL;
}
