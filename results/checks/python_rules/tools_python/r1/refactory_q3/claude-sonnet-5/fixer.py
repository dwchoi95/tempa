from src.core.repair import Rule
import ast
import builtins
from src.core.rewrite import Rewrite


# ---------- helpers ----------

def _parent_chain(node, ctx):
    cur = node
    while cur is not None:
        cur = ctx.parent(cur)
        yield cur


def enclosing_function(node, ctx):
    for p in _parent_chain(node, ctx):
        if isinstance(p, ast.FunctionDef):
            return p
    return None


def enclosing_for(node, ctx):
    for p in _parent_chain(node, ctx):
        if isinstance(p, ast.For):
            return p
    return None


def defined_names(func):
    names = set(a.arg for a in func.args.args)
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            names.add(n.id)
        if isinstance(n, ast.arg):
            names.add(n.arg)
    return names


_BUILTIN_NAMES = set(dir(builtins)) | {"self"}


def is_builtin_name(name):
    return name in _BUILTIN_NAMES


def _lev(a, b):
    if a == b:
        return 0
    la, lb = len(a), len(b)
    dp = [[0] * (lb + 1) for _ in range(la + 1)]
    for i in range(la + 1):
        dp[i][0] = i
    for j in range(lb + 1):
        dp[0][j] = j
    for i in range(1, la + 1):
        for j in range(1, lb + 1):
            cost = 0 if a[i - 1] == b[j - 1] else 1
            dp[i][j] = min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + cost)
    return dp[la][lb]


def _norm(s):
    return s.replace("_", "").lower()


def find_accumulator(func):
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            v = n.value
            if isinstance(v, ast.List) and len(v.elts) == 0:
                return n.targets[0].id, "list"
            if isinstance(v, ast.Tuple) and len(v.elts) == 0:
                return n.targets[0].id, "tuple"
    return None, None


def _find_append_target(stmts):
    for s in stmts:
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
            call = s.value
            if (isinstance(call.func, ast.Attribute) and call.func.attr in ("append", "extend")
                    and isinstance(call.func.value, ast.Name)):
                return call.func.value.id
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            return s.target.id
    return None


# ---------- 1. loop over builtin `list` ----------

def _m_iter_list_builtin(node, ctx):
    return (isinstance(node, ast.Name) and node.id == "list"
            and isinstance(ctx.parent(node), ast.For) and ctx.field(node) == "iter")


def _r_iter_list_builtin(node, ctx):
    func = enclosing_function(node, ctx)
    if func is None or not func.args.args:
        return []
    return [func.args.args[0].arg]


# ---------- 2. for-loop iterates over the (empty) accumulator ----------

def _m_iter_accumulator(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(ctx.parent(node), ast.For) and ctx.field(node) == "iter"):
        return False
    func = enclosing_function(node, ctx)
    if func is None or not func.args.args:
        return False
    param = func.args.args[0].arg
    if node.id == param:
        return False
    accum, _ = find_accumulator(func)
    return accum == node.id


def _r_iter_accumulator(node, ctx):
    func = enclosing_function(node, ctx)
    return [func.args.args[0].arg]


# ---------- 3. for-loop target shadows the parameter / accumulator ----------

def _undefined_ids_in(stmt, func, exclude):
    found = set()
    defined = defined_names(func)
    for n in ast.walk(stmt):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
            if n.id not in defined and not is_builtin_name(n.id) and n.id != exclude:
                found.add(n.id)
    return found


def _m_shadow_target(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(ctx.parent(node), ast.For) and ctx.field(node) == "target"):
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    param = func.args.args[0].arg if func.args.args else None
    accum, _ = find_accumulator(func)
    if not (node.id == param or node.id == accum):
        return False
    forn = ctx.parent(node)
    return len(_undefined_ids_in(forn, func, node.id)) == 1


def _r_shadow_target(node, ctx):
    func = enclosing_function(node, ctx)
    forn = ctx.parent(node)
    cands = _undefined_ids_in(forn, func, node.id)
    return [next(iter(cands))]


# ---------- 4. membership test checks source list instead of accumulator ----------

def _m_bad_membership(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 1 or not isinstance(node.ops[0], (ast.In, ast.NotIn)):
        return False
    if not isinstance(node.comparators[0], ast.Name):
        return False
    func = enclosing_function(node, ctx)
    if func is None or not func.args.args:
        return False
    param = func.args.args[0].arg
    forn = enclosing_for(node, ctx)
    if forn is None:
        return False
    iter_name = forn.iter.id if isinstance(forn.iter, ast.Name) else None
    if node.comparators[0].id not in (param, iter_name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    accum = _find_append_target(parent.body)
    if accum is None or accum == node.comparators[0].id:
        return False
    return True


def _r_bad_membership(node, ctx):
    parent = ctx.parent(node)
    accum = _find_append_target(parent.body)
    op_txt = " not in " if isinstance(node.ops[0], ast.NotIn) else " in "
    return [ctx.text(node.left) + op_txt + accum]


# ---------- 5. undefined-name typo fix ----------

def _is_undefined_name(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    if node.id in defined_names(func) or is_builtin_name(node.id):
        return False
    return True


def _typo_candidates(node, ctx):
    func = enclosing_function(node, ctx)
    names = defined_names(func)
    idn = _norm(node.id)
    out = []
    for cand in names:
        if cand == node.id:
            continue
        cn = _norm(cand)
        if cn == idn:
            out.append(cand)
            continue
        if len(idn) >= 3 and len(cn) >= 3 and _lev(idn, cn) <= 2:
            out.append(cand)
    return out


def _m_typo(node, ctx):
    if not _is_undefined_name(node, ctx):
        return False
    return len(_typo_candidates(node, ctx)) == 1


def _r_typo(node, ctx):
    return [_typo_candidates(node, ctx)[0]]


def _m_undefined_loopvar(node, ctx):
    if not _is_undefined_name(node, ctx):
        return False
    if _typo_candidates(node, ctx):
        return False
    forn = enclosing_for(node, ctx)
    if forn is None or not isinstance(forn.target, ast.Name):
        return False
    return forn.target.id != node.id


def _r_undefined_loopvar(node, ctx):
    forn = enclosing_for(node, ctx)
    return [forn.target.id]


# ---------- 6. `.extend(scalar)` should be `.append(scalar)` ----------

def _m_extend_scalar(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == "extend"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if isinstance(arg, (ast.List, ast.Tuple)):
        return False
    if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == "list":
        return False
    return True


def _r_extend_scalar(node, ctx):
    f = node.func
    return [ctx.text(f.value) + ".append(" + ctx.text(node.args[0]) + ")"]


def _m_extend_list_wrap(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == "extend"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    return (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
            and arg.func.id == "list" and len(arg.args) == 1)


def _r_extend_list_wrap(node, ctx):
    f = node.func
    inner = node.args[0].args[0]
    return [ctx.text(f.value) + ".append(" + ctx.text(inner) + ")"]


# ---------- 7. accumulate scalar with += instead of wrapping ----------

def _m_augassign_add_scalar(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)):
        return False
    if not isinstance(node.target, ast.Name):
        return False
    if isinstance(node.value, (ast.List, ast.Tuple)):
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    accum, kind = find_accumulator(func)
    return accum == node.target.id and kind is not None


def _r_augassign_add_scalar(node, ctx):
    func = enclosing_function(node, ctx)
    _, kind = find_accumulator(func)
    val = ctx.text(node.value)
    wrapped = ("(" + val + ",)") if kind == "tuple" else ("[" + val + "]")
    return [ctx.text(node.target) + " += " + wrapped]


def _m_assign_binop_add_scalar(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    if not isinstance(node.left, ast.Name):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Assign):
        return False
    if len(parent.targets) != 1 or not isinstance(parent.targets[0], ast.Name):
        return False
    if parent.targets[0].id != node.left.id:
        return False
    return not isinstance(node.right, (ast.List, ast.Tuple))


def _r_assign_binop_add_scalar(node, ctx):
    return [ctx.text(node.left) + " + [" + ctx.text(node.right) + "]"]


# ---------- 8. indexing original list instead of its .copy() ----------

def _m_copy_confusion(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Subscript) and parent.value is node):
        return False
    forn = enclosing_for(node, ctx)
    if forn is None or not isinstance(forn.iter, ast.Name):
        return False
    copy_name = forn.iter.id
    if copy_name == node.id:
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == copy_name):
            v = n.value
            if (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)
                    and v.func.attr == "copy" and isinstance(v.func.value, ast.Name)
                    and v.func.value.id == node.id):
                return True
    return False


def _r_copy_confusion(node, ctx):
    forn = enclosing_for(node, ctx)
    return [forn.iter.id]


# ---------- 9. tuple accumulator returned, should be a list ----------

def _m_tuple_return(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == node.value.id):
            if isinstance(n.value, ast.Tuple) and len(n.value.elts) == 0:
                return True
    return False


def _r_tuple_return(node, ctx):
    return ["return list(" + ctx.text(node.value) + ")"]


# ---------- 10. insert(0, x) should be append(x) ----------

def _m_insert_zero(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == "insert"):
        return False
    if len(node.args) != 2:
        return False
    a0 = node.args[0]
    return isinstance(a0, ast.Constant) and a0.value == 0


def _r_insert_zero(node, ctx):
    f = node.func
    return [ctx.text(f.value) + ".append(" + ctx.text(node.args[1]) + ")"]


# ---------- 11. `return None` guarding an empty-list case ----------

def _m_return_none_emptycheck(node, ctx):
    if not isinstance(node, ast.Return):
        return False
    if not (isinstance(node.value, ast.Constant) and node.value.value is None):
        return False
    for p in _parent_chain(node, ctx):
        if isinstance(p, ast.If):
            t = p.test
            if isinstance(t, ast.Compare):
                for c in t.comparators:
                    if isinstance(c, (ast.List, ast.Tuple)) and len(c.elts) == 0:
                        return True
            return False
        if isinstance(p, ast.FunctionDef):
            return False
    return False


def _r_return_none_emptycheck(node, ctx):
    return ["return []"]


# ---------- 12. OrderedDict used without import ----------

def _has_ordereddict_import(ctx):
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.ImportFrom) and n.module == "collections":
            if any(a.name == "OrderedDict" for a in n.names):
                return True
        if isinstance(n, ast.Import):
            if any(a.name == "collections" for a in n.names):
                return True
    return False


def _m_ordereddict_undefined(node, ctx):
    return (isinstance(node, ast.Name) and node.id == "OrderedDict"
            and isinstance(node.ctx, ast.Load) and not _has_ordereddict_import(ctx))


def _r_ordereddict_undefined(node, ctx):
    return ["__import__('collections').OrderedDict"]


def _m_fromkeys_unwrapped(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == "fromkeys"):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name) and parent.func.id == "list":
        return False
    return True


def _r_fromkeys_unwrapped(node, ctx):
    return ["list(" + ctx.text(node) + ")"]


def _is_set_call(node):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "set" and len(node.args) == 1)


def _m_set_call_wrapped(node, ctx):
    if not _is_set_call(node):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name) and parent.func.id == "list"


def _r_set_call_wrapped(node, ctx):
    return ["dict.fromkeys(" + ctx.text(node.args[0]) + ")"]


def _m_set_call_unwrapped(node, ctx):
    return _is_set_call(node) and not _m_set_call_wrapped(node, ctx)


def _r_set_call_unwrapped(node, ctx):
    return ["list(dict.fromkeys(" + ctx.text(node.args[0]) + "))"]


def _m_lists_typo(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "lists" and len(node.args) == 1)


def _r_lists_typo(node, ctx):
    return ["list(" + ctx.text(node.args[0]) + ")"]


# ---------- 13. assigning the result of an in-place mutator ----------

_MUTATORS = {"reverse", "sort", "append", "extend", "remove", "insert", "clear", "pop"}


def _m_assign_inplace_mutator(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    v = node.value
    if not isinstance(v, ast.Call):
        return False
    f = v.func
    return isinstance(f, ast.Attribute) and f.attr in _MUTATORS


def _r_assign_inplace_mutator(node, ctx):
    return [ctx.text(node.value)]


# ---------- 14. a zero-arg list method used without call parens ----------

_ZERO_ARG_METHODS = {"reverse", "sort", "copy", "pop"}


def _m_missing_call_parens(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    if node.attr not in _ZERO_ARG_METHODS:
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    return True


def _r_missing_call_parens(node, ctx):
    return [ctx.text(node) + "()"]


# ---------- 15. `.append.x` instead of `.append(x)` ----------

def _m_attr_dot_misuse(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    v = node.value
    if not isinstance(v, ast.Attribute):
        return False
    return v.attr in ("append", "extend")


def _r_attr_dot_misuse(node, ctx):
    return [ctx.text(node.value) + "(" + node.attr + ")"]


# ---------- 16. `.method[x]` instead of `.method(x)` ----------

_CALL_METHODS = {"count", "append", "extend", "remove", "insert", "pop"}


def _m_subscript_method_call(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    v = node.value
    return isinstance(v, ast.Attribute) and v.attr in _CALL_METHODS


def _r_subscript_method_call(node, ctx):
    sl = node.slice
    if hasattr(ast, "Index") and isinstance(sl, ast.Index):
        sl = sl.value
    return [ctx.text(node.value) + "(" + ctx.text(sl) + ")"]


# ---------- 17. `x == []` used as initialization ----------

def _m_eq_as_init(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    v = node.value
    if not isinstance(v, ast.Compare):
        return False
    if len(v.ops) != 1 or not isinstance(v.ops[0], ast.Eq):
        return False
    if not isinstance(v.left, ast.Name):
        return False
    c = v.comparators[0]
    return isinstance(c, (ast.List, ast.Tuple)) and len(c.elts) == 0


def _r_eq_as_init(node, ctx):
    v = node.value
    return [ctx.text(v.left) + " = " + ctx.text(v.comparators[0])]


# ---------- 18. returning the wrong variable (should be the accumulator) ----------

def _m_return_wrong_var(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = enclosing_function(node, ctx)
    if func is None:
        return False
    accum, _ = find_accumulator(func)
    if accum is None or accum == node.value.id:
        return False
    param = func.args.args[0].arg if func.args.args else None
    loopvar = None
    for n in ast.walk(func):
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name):
            loopvar = n.target.id
            break
    return node.value.id in (param, loopvar)


def _r_return_wrong_var(node, ctx):
    func = enclosing_function(node, ctx)
    accum, _ = find_accumulator(func)
    return ["return " + accum]


# ---------- 19. missing return statement ----------

def _m_missing_return(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if not parent.body or parent.body[-1] is not node:
        return False
    for n in ast.walk(parent):
        if isinstance(n, ast.Return):
            return False
    accum, _ = find_accumulator(parent)
    return accum is not None


def _r_missing_return(node, ctx):
    parent = ctx.parent(node)
    accum, _ = find_accumulator(parent)
    return [ctx.text(node) + "\nreturn " + accum]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="loop_over_builtin_list", match=_m_iter_list_builtin,
                    replace=_r_iter_list_builtin, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="loop_over_empty_accumulator", match=_m_iter_accumulator,
                    replace=_r_iter_accumulator, symptoms=("wrong",)),
            Rewrite(name="for_target_shadows_accum_or_param", match=_m_shadow_target,
                    replace=_r_shadow_target, symptoms=("err:NameError", "wrong")),
            Rewrite(name="membership_against_source_list", match=_m_bad_membership,
                    replace=_r_bad_membership, symptoms=("wrong",)),
            Rewrite(name="undefined_name_typo", match=_m_typo,
                    replace=_r_typo, symptoms=("err:NameError",)),
            Rewrite(name="undefined_name_is_loopvar", match=_m_undefined_loopvar,
                    replace=_r_undefined_loopvar, symptoms=("err:NameError",)),
            Rewrite(name="extend_scalar_to_append", match=_m_extend_scalar,
                    replace=_r_extend_scalar, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="extend_list_wrap_to_append", match=_m_extend_list_wrap,
                    replace=_r_extend_list_wrap, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="augassign_wrap_scalar", match=_m_augassign_add_scalar,
                    replace=_r_augassign_add_scalar, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="assign_binop_wrap_scalar", match=_m_assign_binop_add_scalar,
                    replace=_r_assign_binop_add_scalar, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="index_original_instead_of_copy", match=_m_copy_confusion,
                    replace=_r_copy_confusion, symptoms=("wrong",)),
            Rewrite(name="tuple_accumulator_return_as_list", match=_m_tuple_return,
                    replace=_r_tuple_return, symptoms=("wrong",)),
            Rewrite(name="insert_zero_should_be_append", match=_m_insert_zero,
                    replace=_r_insert_zero, symptoms=("wrong",)),
            Rewrite(name="return_none_should_be_empty_list", match=_m_return_none_emptycheck,
                    replace=_r_return_none_emptycheck, symptoms=("wrong",)),
            Rewrite(name="ordereddict_missing_import", match=_m_ordereddict_undefined,
                    replace=_r_ordereddict_undefined, symptoms=("err:NameError",)),
            Rewrite(name="fromkeys_missing_list_wrap", match=_m_fromkeys_unwrapped,
                    replace=_r_fromkeys_unwrapped, symptoms=("wrong",)),
            Rewrite(name="set_call_wrapped_to_fromkeys", match=_m_set_call_wrapped,
                    replace=_r_set_call_wrapped, symptoms=("wrong",)),
            Rewrite(name="set_call_unwrapped_to_fromkeys", match=_m_set_call_unwrapped,
                    replace=_r_set_call_unwrapped, symptoms=("wrong",)),
            Rewrite(name="lists_typo_to_list", match=_m_lists_typo,
                    replace=_r_lists_typo, symptoms=("err:NameError",)),
            Rewrite(name="assign_result_of_inplace_mutator", match=_m_assign_inplace_mutator,
                    replace=_r_assign_inplace_mutator, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="missing_call_parens", match=_m_missing_call_parens,
                    replace=_r_missing_call_parens, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="attr_dot_instead_of_call", match=_m_attr_dot_misuse,
                    replace=_r_attr_dot_misuse, symptoms=("err:AttributeError", "wrong")),
            Rewrite(name="subscript_instead_of_call", match=_m_subscript_method_call,
                    replace=_r_subscript_method_call, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="eq_used_as_init", match=_m_eq_as_init,
                    replace=_r_eq_as_init, symptoms=("err:NameError", "wrong")),
            Rewrite(name="return_wrong_variable", match=_m_return_wrong_var,
                    replace=_r_return_wrong_var, symptoms=("wrong",)),
            Rewrite(name="missing_return_statement", match=_m_missing_return,
                    replace=_r_missing_return, symptoms=("wrong",)),
        ]