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

/* Forward declarations */
static PyTypeObject ContextType;
static PyTypeObject ExprType;

/* ------------------------------------------------------------------ */
/*  ContextObject (defined first so ExprObject can reference it)      */
/* ------------------------------------------------------------------ */

typedef struct ContextObject {
  PyObject_HEAD ixs_ctx *ctx;
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
  self = PyObject_New(ExprObject, &ExprType);
  if (!self)
    return NULL;
  self->node = node;
  self->ctx_obj = ctx_obj;
  Py_INCREF(ctx_obj);
  return self;
}

static void Expr_dealloc(ExprObject *self) {
  Py_XDECREF(self->ctx_obj);
  Py_TYPE(self)->tp_free((PyObject *)self);
}

/* Coerce a Python object to an ixs_node, extracting ctx from peer Expr. */
static ixs_node *coerce_arg(ContextObject *ctx_obj, PyObject *obj) {
  if (Py_TYPE(obj) == &ExprType) {
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
    return ixs_int(ctx_obj->ctx, (int64_t)v);
  }
  PyErr_SetString(PyExc_TypeError, "ixsimpl: expected Expr or int");
  return NULL;
}

/* Helper: extract ctx from either operand in a binary op. */
static ContextObject *binop_ctx(PyObject *a, PyObject *b) {
  if (Py_TYPE(a) == &ExprType)
    return ((ExprObject *)a)->ctx_obj;
  if (Py_TYPE(b) == &ExprType)
    return ((ExprObject *)b)->ctx_obj;
  return NULL;
}

/* --- repr / str --- */

static PyObject *Expr_repr(ExprObject *self) {
  char buf[8192];
  if (ixs_is_error(self->node))
    return PyUnicode_FromString("<error>");
  ixs_print(self->node, buf, sizeof(buf));
  return PyUnicode_FromString(buf);
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
    if (Py_TYPE(other) == &ExprType) {
      if (((ExprObject *)other)->node == self->node)
        Py_RETURN_TRUE;
      Py_RETURN_FALSE;
    }
    Py_RETURN_NOTIMPLEMENTED;
  }
  if (op == Py_NE) {
    if (Py_TYPE(other) == &ExprType) {
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

  result = ixs_cmp(ctx_obj->ctx, a, cmp, b);
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
  result = ixs_add(ctx_obj->ctx, na, nb);
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
  result = ixs_sub(ctx_obj->ctx, na, nb);
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
  result = ixs_mul(ctx_obj->ctx, na, nb);
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
  result = ixs_div(ctx_obj->ctx, na, nb);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *Expr_neg(ExprObject *self) {
  ixs_node *result = ixs_neg(self->ctx_obj->ctx, self->node);
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
    if (n > 0) {
      assumptions = PyMem_Malloc((size_t)n * sizeof(ixs_node *));
      if (!assumptions)
        return PyErr_NoMemory();
      for (i = 0; i < n; i++) {
        PyObject *item = PySequence_GetItem(assumptions_obj, i);
        if (!item || Py_TYPE(item) != &ExprType) {
          Py_XDECREF(item);
          PyMem_Free(assumptions);
          PyErr_SetString(PyExc_TypeError, "each assumption must be an Expr");
          return NULL;
        }
        assumptions[i] = ((ExprObject *)item)->node;
        Py_DECREF(item);
      }
      n_assumptions = (size_t)n;
    }
  }

  result =
      ixs_simplify(self->ctx_obj->ctx, self->node, assumptions, n_assumptions);
  PyMem_Free(assumptions);
  return (PyObject *)Expr_wrap(self->ctx_obj, result);
}

static PyObject *Expr_to_c(ExprObject *self, PyObject *Py_UNUSED(args)) {
  char buf[8192];
  if (ixs_is_error(self->node))
    return PyUnicode_FromString("/* error */");
  ixs_print_c(self->node, buf, sizeof(buf));
  return PyUnicode_FromString(buf);
}

static PyObject *Expr_subs(ExprObject *self, PyObject *args) {
  PyObject *target_obj, *repl_obj;
  ixs_node *target, *repl, *result;

  if (!PyArg_ParseTuple(args, "OO", &target_obj, &repl_obj))
    return NULL;

  /* Accept string as shorthand for symbol lookup */
  if (PyUnicode_Check(target_obj)) {
    const char *name = PyUnicode_AsUTF8(target_obj);
    if (!name)
      return NULL;
    target = ixs_sym(self->ctx_obj->ctx, name);
  } else {
    target = coerce_arg(self->ctx_obj, target_obj);
  }
  if (!target)
    return NULL;

  repl = coerce_arg(self->ctx_obj, repl_obj);
  if (!repl)
    return NULL;

  result = ixs_subs(self->ctx_obj->ctx, self->node, target, repl);
  return (PyObject *)Expr_wrap(self->ctx_obj, result);
}

static PyMethodDef Expr_methods[] = {
    {"simplify", (PyCFunction)Expr_simplify, METH_VARARGS | METH_KEYWORDS,
     "Simplify expression with optional assumptions."},
    {"to_c", (PyCFunction)Expr_to_c, METH_NOARGS,
     "Return C code representation."},
    {"subs", (PyCFunction)Expr_subs, METH_VARARGS,
     "expr.subs(target, replacement): target is str (variable name) or Expr "
     "(any subexpression); replacement is Expr or int."},
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

static PyObject *Expr_get_tag(ExprObject *self, void *Py_UNUSED(closure)) {
  return PyLong_FromLong((long)ixs_node_tag(self->node));
}

static PyGetSetDef Expr_getset[] = {
    {"is_error", (getter)Expr_get_is_error, NULL,
     "True if node is any error sentinel.", NULL},
    {"is_parse_error", (getter)Expr_get_is_parse_error, NULL,
     "True if node is a parse error sentinel.", NULL},
    {"is_domain_error", (getter)Expr_get_is_domain_error, NULL,
     "True if node is a domain error sentinel.", NULL},
    {"tag", (getter)Expr_get_tag, NULL, "Node type tag (ixs_tag enum).", NULL},
    {NULL}};

static PyTypeObject ExprType = {
    .ob_base = PyVarObject_HEAD_INIT(NULL, 0).tp_name = "ixsimpl.Expr",
    .tp_basicsize = sizeof(ExprObject),
    .tp_dealloc = (destructor)Expr_dealloc,
    .tp_repr = (reprfunc)Expr_repr,
    .tp_as_number = &Expr_as_number,
    .tp_hash = (hashfunc)Expr_hash,
    .tp_str = (reprfunc)Expr_str,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_doc = "ixsimpl expression node.",
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
  self->ctx = ixs_ctx_create();
  if (!self->ctx) {
    Py_DECREF(self);
    PyErr_SetString(PyExc_MemoryError, "ixsimpl: failed to create context");
    return NULL;
  }
  return (PyObject *)self;
}

static void Context_dealloc(ContextObject *self) {
  if (self->ctx)
    ixs_ctx_destroy(self->ctx);
  Py_TYPE(self)->tp_free((PyObject *)self);
}

/* --- Context methods --- */

static PyObject *Context_sym(ContextObject *self, PyObject *args) {
  const char *name;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "s", &name))
    return NULL;
  node = ixs_sym(self->ctx, name);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_parse(ContextObject *self, PyObject *args) {
  const char *input;
  Py_ssize_t len;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "s#", &input, &len))
    return NULL;
  node = ixs_parse(self->ctx, input, (size_t)len);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_int_(ContextObject *self, PyObject *args) {
  long long val;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "L", &val))
    return NULL;
  node = ixs_int(self->ctx, (int64_t)val);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_rat(ContextObject *self, PyObject *args) {
  long long p, q;
  ixs_node *node;
  if (!PyArg_ParseTuple(args, "LL", &p, &q))
    return NULL;
  node = ixs_rat(self->ctx, (int64_t)p, (int64_t)q);
  return (PyObject *)Expr_wrap(self, node);
}

static PyObject *Context_true_(ContextObject *self, PyObject *Py_UNUSED(args)) {
  return (PyObject *)Expr_wrap(self, ixs_true(self->ctx));
}

static PyObject *Context_false_(ContextObject *self,
                                PyObject *Py_UNUSED(args)) {
  return (PyObject *)Expr_wrap(self, ixs_false(self->ctx));
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
  result = ixs_cmp(self->ctx, a, IXS_CMP_EQ, b);
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
  result = ixs_cmp(self->ctx, a, IXS_CMP_NE, b);
  return (PyObject *)Expr_wrap(self, result);
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
    if (Py_TYPE(item) != &ExprType) {
      PyMem_Free(exprs);
      PyErr_SetString(PyExc_TypeError, "each expr must be an Expr");
      return NULL;
    }
    exprs[i] = ((ExprObject *)item)->node;
  }

  if (assumptions_obj && assumptions_obj != Py_None &&
      PySequence_Size(assumptions_obj) > 0) {
    n_assumptions = PySequence_Size(assumptions_obj);
    assumptions = PyMem_Malloc((size_t)n_assumptions * sizeof(ixs_node *));
    if (!assumptions) {
      PyMem_Free(exprs);
      return PyErr_NoMemory();
    }
    for (i = 0; i < n_assumptions; i++) {
      PyObject *item = PySequence_GetItem(assumptions_obj, i);
      if (!item || Py_TYPE(item) != &ExprType) {
        Py_XDECREF(item);
        PyMem_Free(exprs);
        PyMem_Free(assumptions);
        PyErr_SetString(PyExc_TypeError, "each assumption must be an Expr");
        return NULL;
      }
      assumptions[i] = ((ExprObject *)item)->node;
      Py_DECREF(item);
    }
  }

  ixs_simplify_batch(self->ctx, exprs, (size_t)n_exprs, assumptions,
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
  ixs_ctx_clear_errors(self->ctx);
  Py_RETURN_NONE;
}

static PyMethodDef Context_methods[] = {
    {"sym", (PyCFunction)Context_sym, METH_VARARGS,
     "Create a symbol: ctx.sym('x')."},
    {"parse", (PyCFunction)Context_parse, METH_VARARGS,
     "Parse a SymPy-like expression string."},
    {"int_", (PyCFunction)Context_int_, METH_VARARGS,
     "Create an integer node: ctx.int_(42)."},
    {"rat", (PyCFunction)Context_rat, METH_VARARGS,
     "Create a rational node: ctx.rat(1, 3)."},
    {"true_", (PyCFunction)Context_true_, METH_NOARGS, "Return True node."},
    {"false_", (PyCFunction)Context_false_, METH_NOARGS, "Return False node."},
    {"eq", (PyCFunction)Context_eq, METH_VARARGS,
     "Build an equality CMP node: ctx.eq(a, b)."},
    {"ne", (PyCFunction)Context_ne, METH_VARARGS,
     "Build an inequality CMP node: ctx.ne(a, b)."},
    {"simplify_batch", (PyCFunction)Context_simplify_batch,
     METH_VARARGS | METH_KEYWORDS, "Simplify a list of Expr in-place."},
    {"clear_errors", (PyCFunction)Context_clear_errors, METH_NOARGS,
     "Clear the error list."},
    {NULL}};

/* --- Context properties --- */

static PyObject *Context_get_errors(ContextObject *self,
                                    void *Py_UNUSED(closure)) {
  size_t n = ixs_ctx_nerrors(self->ctx);
  size_t i;
  PyObject *list = PyList_New((Py_ssize_t)n);
  if (!list)
    return NULL;
  for (i = 0; i < n; i++) {
    const char *msg = ixs_ctx_error(self->ctx, i);
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
  if (Py_TYPE(arg) != &ExprType) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.floor() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_floor(e->ctx_obj->ctx, e->node);
  return (PyObject *)Expr_wrap(e->ctx_obj, result);
}

static PyObject *mod_ceil(PyObject *Py_UNUSED(module), PyObject *arg) {
  ExprObject *e;
  ixs_node *result;
  if (Py_TYPE(arg) != &ExprType) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.ceil() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_ceil(e->ctx_obj->ctx, e->node);
  return (PyObject *)Expr_wrap(e->ctx_obj, result);
}

static PyObject *mod_binary_op(PyObject *args,
                               ixs_node *(*op)(ixs_ctx *, ixs_node *,
                                               ixs_node *),
                               const char *name) {
  PyObject *a_obj, *b_obj;
  ExprObject *ae;
  ixs_node *a, *b, *result;

  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;

  if (Py_TYPE(a_obj) != &ExprType) {
    PyErr_Format(PyExc_TypeError, "ixsimpl.%s() first arg must be Expr", name);
    return NULL;
  }
  ae = (ExprObject *)a_obj;
  a = ae->node;
  b = coerce_arg(ae->ctx_obj, b_obj);
  if (!b)
    return NULL;

  result = op(ae->ctx_obj->ctx, a, b);
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
  if (Py_TYPE(arg) != &ExprType) {
    PyErr_SetString(PyExc_TypeError, "ixsimpl.not_() requires an Expr");
    return NULL;
  }
  e = (ExprObject *)arg;
  result = ixs_not(e->ctx_obj->ctx, e->node);
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
      if (Py_TYPE(val_obj) == &ExprType)
        ctx_obj = ((ExprObject *)val_obj)->ctx_obj;
      else if (Py_TYPE(cond_obj) == &ExprType)
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

  result = ixs_pw(ctx_obj->ctx, (uint32_t)n, values, conds);
  PyMem_Free(values);
  PyMem_Free(conds);
  return (PyObject *)Expr_wrap(ctx_obj, result);
}

static PyObject *mod_same_node(PyObject *Py_UNUSED(module), PyObject *args) {
  PyObject *a_obj, *b_obj;
  if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj))
    return NULL;
  if (Py_TYPE(a_obj) != &ExprType || Py_TYPE(b_obj) != &ExprType) {
    PyErr_SetString(PyExc_TypeError,
                    "ixsimpl.same_node() requires two Expr arguments");
    return NULL;
  }
  return PyBool_FromLong(
      ixs_same_node(((ExprObject *)a_obj)->node, ((ExprObject *)b_obj)->node));
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
    {NULL}};

/* ------------------------------------------------------------------ */
/*  Module init                                                       */
/* ------------------------------------------------------------------ */

static struct PyModuleDef ixsimpl_module = {
    .m_base = PyModuleDef_HEAD_INIT,
    .m_name = "ixsimpl",
    .m_doc = "Index expression simplifier — fast symbolic integer arithmetic.",
    .m_size = -1,
    .m_methods = module_methods,
};

PyMODINIT_FUNC PyInit_ixsimpl(void) {
  PyObject *m;

  if (PyType_Ready(&ContextType) < 0)
    return NULL;
  if (PyType_Ready(&ExprType) < 0)
    return NULL;

  m = PyModule_Create(&ixsimpl_module);
  if (!m)
    return NULL;

  Py_INCREF(&ContextType);
  if (PyModule_AddObject(m, "Context", (PyObject *)&ContextType) < 0) {
    Py_DECREF(&ContextType);
    Py_DECREF(m);
    return NULL;
  }

  Py_INCREF(&ExprType);
  if (PyModule_AddObject(m, "Expr", (PyObject *)&ExprType) < 0) {
    Py_DECREF(&ExprType);
    Py_DECREF(m);
    return NULL;
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

  return m;
}
