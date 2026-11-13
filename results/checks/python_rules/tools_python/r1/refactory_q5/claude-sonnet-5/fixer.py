from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _enclosing_function(node, ctx):
    n = node
    while True:
        n = ctx.parent(n)
        if n is None:
            return None
        if isinstance(n, ast.FunctionDef):
            return n


def _enclosing_stmt_and_body(node, ctx):
    n = node
    while True:
        p = ctx.parent(n)
        if p is None:
            return None, None, None
        field = ctx.field(n)
        val = getattr(p, field, None)
        if isinstance(val, list) and n in val:
            return p, field, val
        n = p


def _slice_value_text(node, ctx):
    s = node.slice
    if isinstance(s, ast.Index):
        return ctx.text(s.value)
    return ctx.text(s)


# 1. off-by-one literal offset applied to a slice upper bound ([:k+1], [:k-1])
def _is_offby1_slice_binop(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub))):
        return False
    if not (isinstance(node.right, ast.Constant) and node.right.value == 1):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Slice) and parent.upper is node


def _fix_offby1_slice_binop(node, ctx):
    return [ctx.text(node.left)]


# 2. a hard-coded numeric slice bound should be the k parameter
def _is_hardcoded_slice(node, ctx):
    if not (isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice)):
        return False
    sl = node.slice
    if sl.lower is not None or sl.step is not None:
        return False
    return isinstance(sl.upper, ast.Constant) and isinstance(sl.upper.value, int)


def _fix_hardcoded_slice(node, ctx):
    func = _enclosing_function(node, ctx)
    if not func or not func.args.args:
        return []
    k_param = func.args.args[-1].arg
    return [ctx.text(node.value) + "[:" + k_param + "]"]


# 3. counting loop initialised at 0 but bounded with <=k / !=k style
def _zero_init(func, name, is_len):
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and n.targets[0].id == name:
            if is_len:
                if isinstance(n.value, ast.List) and len(n.value.elts) == 0:
                    return True
            else:
                if isinstance(n.value, ast.Constant) and n.value.value == 0:
                    return True
    return False


def _is_offby1_counter_lte(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    left = node.left
    if isinstance(left, ast.Name):
        if not _zero_init(func, left.id, False):
            return False
    elif isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == 'len' \
            and len(left.args) == 1 and isinstance(left.args[0], ast.Name):
        if not _zero_init(func, left.args[0].id, True):
            return False
    else:
        return False
    comp = node.comparators[0]
    if not isinstance(comp, ast.Name):
        return False
    return comp.id in [a.arg for a in func.args.args]


def _fix_offby1_counter_lte(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


# 4. while k >= 0 decrement loop should be while k > 0
def _is_k_ge_zero(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)):
        return False
    if not (isinstance(node.left, ast.Name) and isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 0):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.While) and parent.test is node


def _fix_k_ge_zero(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


# 5. extremum-tracking comparison finds the minimum instead of the maximum
def _is_min_tracker(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], (ast.Lt, ast.LtE))):
        return False
    if not (isinstance(node.left, ast.Name) and len(node.comparators) == 1
            and isinstance(node.comparators[0], ast.Name)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    if len(parent.body) != 1 or not isinstance(parent.body[0], ast.Assign):
        return False
    assign = parent.body[0]
    if len(assign.targets) != 1 or not isinstance(assign.targets[0], ast.Name) \
            or not isinstance(assign.value, ast.Name):
        return False
    names = {node.left.id, node.comparators[0].id}
    tgt, val = assign.targets[0].id, assign.value.id
    return tgt in names and val in names and tgt != val


def _fix_min_tracker(node, ctx):
    op = " >= " if isinstance(node.ops[0], ast.LtE) else " > "
    return [ctx.text(node.left) + op + ctx.text(node.comparators[0])]


# 6. extremum-tracking if body assigns the wrong variable
def _is_if_body_wrong_target(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name) and isinstance(node.value, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and len(parent.body) == 1 and parent.body[0] is node):
        return False
    test = parent.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], (ast.Gt, ast.Lt, ast.GtE, ast.LtE))
            and isinstance(test.left, ast.Name) and len(test.comparators) == 1
            and isinstance(test.comparators[0], ast.Name)):
        return False
    names = {test.left.id, test.comparators[0].id}
    val = node.value.id
    if val not in names:
        return False
    other = test.left.id if val == test.comparators[0].id else test.comparators[0].id
    tgt = node.targets[0].id
    return tgt != other


def _fix_if_body_wrong_target(node, ctx):
    test = ctx.parent(node).test
    val = node.value.id
    other = test.left.id if val == test.comparators[0].id else test.comparators[0].id
    return [other + " = " + ctx.text(node.value)]


# 7. append/remove uses a variable other than the loop's tracked maximum
def _find_track_var(node, ctx):
    n = node
    loop = None
    while True:
        n = ctx.parent(n)
        if n is None:
            return None
        if isinstance(n, ast.While):
            loop = n
            break
    if not loop.body:
        return None
    s = loop.body[0]
    if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) \
            and isinstance(s.value, ast.Subscript):
        sl = s.value.slice
        val = sl.value if isinstance(sl, ast.Index) else sl
        if isinstance(val, ast.Constant) and val.value == 0:
            return s.targets[0].id
    return None


def _is_track_mismatch(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in ('append', 'remove') and len(node.args) == 1
            and isinstance(node.args[0], ast.Name)):
        return False
    track = _find_track_var(node, ctx)
    if track is None:
        return False
    return node.args[0].id != track


def _fix_track_mismatch(node, ctx):
    track = _find_track_var(node, ctx)
    return [ctx.text(node.func) + "(" + track + ")"]


# 8. a[i] used where a call was meant: r.append[x] / lst.remove[x]
def _is_bracket_call(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr in ('append', 'remove', 'pop'))


def _fix_bracket_call(node, ctx):
    return [ctx.text(node.value) + "(" + _slice_value_text(node, ctx) + ")"]


# 9. append(param_list) right after computing the max, should append the computed value
def _is_append_param_self(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'append' and len(node.args) == 1):
        return False
    arg = node.args[0]
    if not isinstance(arg, ast.Name):
        return False
    func = _enclosing_function(node, ctx)
    if not func or not func.args.args:
        return False
    first_param = func.args.args[0].arg
    if arg.id != first_param:
        return False
    stmt, field, body = _enclosing_stmt_and_body(node, ctx)
    if stmt is None:
        return False
    idx = body.index(stmt)
    if idx == 0:
        return False
    prev = body[idx - 1]
    if not (isinstance(prev, ast.Assign) and len(prev.targets) == 1
            and isinstance(prev.targets[0], ast.Name)):
        return False
    val = prev.value
    return (isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == 'max'
            and len(val.args) == 1 and isinstance(val.args[0], ast.Name)
            and val.args[0].id == first_param)


def _fix_append_param_self(node, ctx):
    stmt, field, body = _enclosing_stmt_and_body(node, ctx)
    idx = body.index(stmt)
    prev = body[idx - 1]
    varname = prev.targets[0].id
    return [ctx.text(node.func) + "(" + varname + ")"]


# 10. returning a slice of the original list instead of the built-up accumulator
def _is_return_uses_param(node, ctx):
    if not (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Return):
        return False
    func = _enclosing_function(node, ctx)
    if not func or not func.args.args:
        return False
    return node.value.id == func.args.args[0].arg


def _fix_return_uses_param(node, ctx):
    func = _enclosing_function(node, ctx)
    first_param = func.args.args[0].arg
    cand = None
    for n in func.body:
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and isinstance(n.value, ast.List) and len(n.value.elts) == 0 \
                and n.targets[0].id != first_param:
            cand = n.targets[0].id
    if cand is None:
        return []
    return [cand + "[" + _slice_value_text(node, ctx) + "]"]


# 11. function never returns the accumulator it built
def _find_append_target(loop):
    for n in ast.walk(loop):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == 'append' \
                and isinstance(n.func.value, ast.Name):
            return n.func.value.id
    return None


def _is_missing_return(node, ctx):
    if not isinstance(node, (ast.While, ast.For)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or not func.body or func.body[-1] is not node:
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Return):
            return False
    return _find_append_target(node) is not None


def _fix_missing_return(node, ctx):
    name = _find_append_target(node)
    return [ctx.text(node) + "\nreturn " + name]


# 12. generic undefined-name typo resolved to the unique list accumulator
_BUILTIN_NAMES = {'max', 'min', 'len', 'list', 'range', 'int', 'str', 'sorted',
                   'abs', 'sum', 'print', 'True', 'False', 'None'}


def _collect_bound_names(func):
    bound = set(a.arg for a in func.args.args)
    bound.add(func.name)
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                for nm in ast.walk(t):
                    if isinstance(nm, ast.Name):
                        bound.add(nm.id)
        elif isinstance(n, ast.AugAssign):
            if isinstance(n.target, ast.Name):
                bound.add(n.target.id)
        elif isinstance(n, ast.For):
            for nm in ast.walk(n.target):
                if isinstance(nm, ast.Name):
                    bound.add(nm.id)
    return bound


def _find_list_candidate(func, exclude):
    empties, copies = [], []
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            tid = n.targets[0].id
            if tid == exclude:
                continue
            if isinstance(n.value, ast.List) and len(n.value.elts) == 0:
                empties.append(tid)
            elif isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Attribute) \
                    and n.value.func.attr == 'copy':
                copies.append(tid)
    cands = list(dict.fromkeys(empties + copies))
    return cands[0] if len(cands) == 1 else None


def _is_undefined_name(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    if node.id in _BUILTIN_NAMES:
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    if node.id in _collect_bound_names(func):
        return False
    return _find_list_candidate(func, node.id) is not None


def _fix_undefined_name(node, ctx):
    func = _enclosing_function(node, ctx)
    cand = _find_list_candidate(func, node.id)
    return [cand] if cand else []


# 13. extending with the loop index itself instead of the list element at that index
def _is_extend_bare_index(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'extend'):
        return False
    if len(node.args) != 1 or not isinstance(node.args[0], ast.List) or len(node.args[0].elts) != 1:
        return False
    return isinstance(node.args[0].elts[0], ast.Name)


def _fix_extend_bare_index(node, ctx):
    elt = node.args[0].elts[0]
    func = _enclosing_function(node, ctx)
    if func is None:
        return []
    target_list = None
    for n in ast.walk(func):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name):
            sl = n.slice
            idx = sl.value if isinstance(sl, ast.Index) else sl
            if isinstance(idx, ast.Name) and idx.id == elt.id:
                target_list = n.value.id
                break
    if target_list is None:
        return []
    return [ctx.text(node.func) + "([" + target_list + "[" + elt.id + "]])"]


# 14. comparing the range index directly instead of indexing the list
def _is_range_index_as_value(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    left = node.left
    right = node.comparators[0]
    if not isinstance(left, ast.Name):
        return False
    if not (isinstance(right, ast.Call) and isinstance(right.func, ast.Name) and right.func.id == 'max'
            and len(right.args) == 1 and isinstance(right.args[0], ast.Name)):
        return False
    L = right.args[0].id
    n = node
    for_loop = None
    while True:
        n = ctx.parent(n)
        if n is None:
            break
        if isinstance(n, ast.For):
            for_loop = n
            break
    if for_loop is None or not isinstance(for_loop.target, ast.Name) or for_loop.target.id != left.id:
        return False
    it = for_loop.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == 'range'
            and len(it.args) == 1):
        return False
    inner = it.args[0]
    return (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) and inner.func.id == 'len'
            and len(inner.args) == 1 and isinstance(inner.args[0], ast.Name) and inner.args[0].id == L)


def _fix_range_index_as_value(node, ctx):
    left = node.left
    right = node.comparators[0]
    L = right.args[0].id
    return [L + "[" + left.id + "] == " + ctx.text(right)]


# 15. missing k==0 guard alongside an empty-list guard
def _is_lst_empty_check(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    if not (isinstance(node.left, ast.Name) and isinstance(node.comparators[0], ast.List)
            and len(node.comparators[0].elts) == 0):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    func = _enclosing_function(node, ctx)
    if not func or len(func.args.args) < 2:
        return False
    if node.left.id != func.args.args[0].arg:
        return False
    if len(parent.body) != 1 or not isinstance(parent.body[0], ast.Return):
        return False
    retval = parent.body[0].value
    return isinstance(retval, ast.List) and len(retval.elts) == 0


def _fix_lst_empty_check(node, ctx):
    func = _enclosing_function(node, ctx)
    k_param = func.args.args[-1].arg
    return [ctx.text(node) + " or " + k_param + " == 0"]


# 16. range(-len(lst), -1) excludes the last element; should be range(-len(lst), 0)
def _is_neg_range_offby1(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'range'
            and len(node.args) == 2):
        return False
    a0, a1 = node.args
    if not (isinstance(a0, ast.UnaryOp) and isinstance(a0.op, ast.USub)
            and isinstance(a0.operand, ast.Call) and isinstance(a0.operand.func, ast.Name)
            and a0.operand.func.id == 'len'):
        return False
    return (isinstance(a1, ast.UnaryOp) and isinstance(a1.op, ast.USub)
            and isinstance(a1.operand, ast.Constant) and a1.operand.value == 1)


def _fix_neg_range_offby1(node, ctx):
    return [ctx.text(node.func) + "(" + ctx.text(node.args[0]) + ", 0)"]


# 17. missing counter increment inside a counting loop
def _is_missing_counter_incr(node, ctx):
    if not isinstance(node, ast.While):
        return False
    test = node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.Lt)
            and isinstance(test.left, ast.Name)):
        return False
    counter = test.left.id
    for s in ast.walk(node):
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and s.target.id == counter:
            return False
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) \
                and s.targets[0].id == counter and isinstance(s.value, ast.BinOp):
            return False
    func = _enclosing_function(node, ctx)
    return func is not None and any(isinstance(n, ast.Assign) and len(n.targets) == 1
                                     and isinstance(n.targets[0], ast.Name) and n.targets[0].id == counter
                                     and isinstance(n.value, ast.Constant) and n.value.value == 0
                                     for n in func.body)


def _fix_missing_counter_incr(node, ctx):
    counter = node.test.left.id
    body_texts = [ctx.text(s) for s in node.body]
    body_texts.append(counter + " += 1")
    header = "while " + ctx.text(node.test) + ":"
    return [header + "\n" + "\n".join("    " + t for t in body_texts)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="offby1_slice_binop", match=_is_offby1_slice_binop,
                    replace=_fix_offby1_slice_binop, symptoms=("wrong",)),
            Rewrite(name="hardcoded_slice_bound", match=_is_hardcoded_slice,
                    replace=_fix_hardcoded_slice, symptoms=("wrong",)),
            Rewrite(name="offby1_counter_lte", match=_is_offby1_counter_lte,
                    replace=_fix_offby1_counter_lte, symptoms=("wrong", "timeout")),
            Rewrite(name="k_ge_zero_loop", match=_is_k_ge_zero,
                    replace=_fix_k_ge_zero, symptoms=("wrong",)),
            Rewrite(name="min_tracker_should_be_max", match=_is_min_tracker,
                    replace=_fix_min_tracker, symptoms=("wrong",)),
            Rewrite(name="if_body_wrong_target", match=_is_if_body_wrong_target,
                    replace=_fix_if_body_wrong_target, symptoms=("wrong",)),
            Rewrite(name="append_remove_track_var_mismatch", match=_is_track_mismatch,
                    replace=_fix_track_mismatch, symptoms=("wrong", "err:NameError")),
            Rewrite(name="bracket_instead_of_call", match=_is_bracket_call,
                    replace=_fix_bracket_call, symptoms=("err:TypeError",)),
            Rewrite(name="append_param_should_be_computed_max", match=_is_append_param_self,
                    replace=_fix_append_param_self, symptoms=("wrong",)),
            Rewrite(name="return_uses_param_not_accumulator", match=_is_return_uses_param,
                    replace=_fix_return_uses_param, symptoms=("wrong",)),
            Rewrite(name="missing_return_accumulator", match=_is_missing_return,
                    replace=_fix_missing_return, symptoms=("wrong",)),
            Rewrite(name="undefined_name_fallback", match=_is_undefined_name,
                    replace=_fix_undefined_name, symptoms=("err:NameError",)),
            Rewrite(name="extend_bare_index", match=_is_extend_bare_index,
                    replace=_fix_extend_bare_index, symptoms=("wrong",)),
            Rewrite(name="range_index_used_as_value", match=_is_range_index_as_value,
                    replace=_fix_range_index_as_value, symptoms=("wrong", "timeout")),
            Rewrite(name="missing_k_zero_guard", match=_is_lst_empty_check,
                    replace=_fix_lst_empty_check, symptoms=("wrong",)),
            Rewrite(name="neg_range_offby1", match=_is_neg_range_offby1,
                    replace=_fix_neg_range_offby1, symptoms=("wrong",)),
            Rewrite(name="missing_counter_increment", match=_is_missing_counter_incr,
                    replace=_fix_missing_counter_incr, symptoms=("timeout",)),
        ]