from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------- helpers ----------

def _enclosing_function(node, ctx):
    cur = node
    while cur is not None:
        if isinstance(cur, ast.FunctionDef):
            return cur
        cur = ctx.parent(cur)
    return None


def _k_param_name(node, ctx):
    fn = _enclosing_function(node, ctx)
    if fn is None or len(fn.args.args) < 2:
        return None
    return fn.args.args[1].arg


def _get_siblings(node, ctx):
    parent = ctx.parent(node)
    field = ctx.field(node)
    if parent is None or field is None:
        return None, None
    body = getattr(parent, field, None)
    if not isinstance(body, list) or node not in body:
        return None, None
    return body, body.index(node)


def _is_call_attr(node, names):
    if isinstance(names, str):
        names = (names,)
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in names)


def _stmt_call(stmt, methodname):
    if isinstance(stmt, ast.Expr) and _is_call_attr(stmt.value, methodname):
        return stmt.value
    return None


def _slice_expr(s):
    if isinstance(s, ast.Index):  # py<3.9 compatibility
        return s.value
    return s


def _walk_no_nested_func(node):
    for child in ast.iter_child_nodes(node):
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
            continue
        yield child
        yield from _walk_no_nested_func(child)


def _contains_return(fn):
    for s in fn.body:
        if isinstance(s, ast.Return):
            return True
        for n in _walk_no_nested_func(s):
            if isinstance(n, ast.Return):
                return True
    return False


def _find_empty_list_acc(fn):
    for s in fn.body:
        if (isinstance(s, ast.Assign) and len(s.targets) == 1
                and isinstance(s.targets[0], ast.Name)
                and isinstance(s.value, ast.List) and len(s.value.elts) == 0):
            return s.targets[0].id
    return None


def _enclosing_for(node, ctx):
    cur = node
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.For):
            return cur
        if isinstance(cur, ast.FunctionDef):
            return None
    return None


def _find_reseed(whilenode):
    if not isinstance(whilenode, ast.While) or len(whilenode.body) < 2:
        return None
    last = whilenode.body[-1]
    if not (isinstance(last, ast.Assign) and len(last.targets) == 1
            and isinstance(last.targets[0], ast.Name)):
        return None
    if not isinstance(last.value, ast.Subscript):
        return None
    sl = _slice_expr(last.value.slice)
    if isinstance(sl, ast.Constant) and sl.value == 0:
        return last
    return None


# ---------- 1/2: remove-before-append should be append-before-remove ----------

def _match_remove_before_append(node, ctx):
    call = _stmt_call(node, "remove")
    if call is None or not call.args:
        return False
    body, idx = _get_siblings(node, ctx)
    if body is None or idx + 1 >= len(body):
        return False
    call2 = _stmt_call(body[idx + 1], "append")
    if call2 is None or not call2.args:
        return False
    return ast.dump(call.args[0]) == ast.dump(call2.args[0])


def _fix_remove_before_append_delete(node, ctx):
    return [""]


def _match_append_after_remove(node, ctx):
    call = _stmt_call(node, "append")
    if call is None or not call.args:
        return False
    body, idx = _get_siblings(node, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    call2 = _stmt_call(prev, "remove")
    if call2 is None or not call2.args:
        return False
    return ast.dump(call.args[0]) == ast.dump(call2.args[0])


def _fix_append_after_remove(node, ctx):
    body, idx = _get_siblings(node, ctx)
    prev = body[idx - 1]
    return [ctx.text(node) + "\n" + ctx.text(prev)]


# ---------- 3: wrong assign target while tracking max/min ----------

def _match_max_track_wrong_target(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    parent_if = ctx.parent(node)
    if not isinstance(parent_if, ast.If) or len(parent_if.body) != 1 or parent_if.body[0] is not node:
        return False
    test = parent_if.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], (ast.Gt, ast.Lt))):
        return False
    left, right = test.left, test.comparators[0]
    if not (isinstance(left, ast.Name) and isinstance(right, ast.Name)):
        return False
    forn = _enclosing_for(parent_if, ctx)
    if forn is None or not isinstance(forn.target, ast.Name):
        return False
    loop_var = forn.target.id
    names = {left.id, right.id}
    if loop_var not in names or len(names) != 2:
        return False
    acc_name = (names - {loop_var}).pop()
    return node.targets[0].id != acc_name


def _fix_max_track_wrong_target(node, ctx):
    parent_if = ctx.parent(node)
    test = parent_if.test
    left, right = test.left, test.comparators[0]
    forn = _enclosing_for(parent_if, ctx)
    loop_var = forn.target.id
    names = {left.id, right.id}
    acc_name = (names - {loop_var}).pop()
    return [f"{acc_name} = {loop_var}"]


# ---------- 4: append uses wrong variable right after a remove() call ----------

def _match_append_wrong_var(node, ctx):
    if not (isinstance(node, ast.Call) and _is_call_attr(node, "append")):
        return False
    if len(node.args) != 1 or not isinstance(node.args[0], ast.Name):
        return False
    stmt = ctx.parent(node)
    if not isinstance(stmt, ast.Expr):
        return False
    body, idx = _get_siblings(stmt, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    remove_call = _stmt_call(prev, "remove")
    if remove_call is None or len(remove_call.args) != 1 or not isinstance(remove_call.args[0], ast.Name):
        return False
    return remove_call.args[0].id != node.args[0].id


def _fix_append_wrong_var(node, ctx):
    stmt = ctx.parent(node)
    body, idx = _get_siblings(stmt, ctx)
    prev = body[idx - 1]
    remove_call = _stmt_call(prev, "remove")
    good_name = remove_call.args[0].id
    return [ctx.text(node.func) + "(" + good_name + ")"]


# ---------- 5/6: bad slice bound ----------

def _match_slice_binop_bound(node, ctx):
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, (ast.Add, ast.Sub)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Slice) or parent.upper is not node:
        return False
    if parent.lower is not None or parent.step is not None:
        return False
    kname = _k_param_name(node, ctx)
    if kname is None:
        return False
    operands = [node.left, node.right]
    namepart = [o for o in operands if isinstance(o, ast.Name) and o.id == kname]
    constpart = [o for o in operands if isinstance(o, ast.Constant) and isinstance(o.value, int)]
    return len(namepart) == 1 and len(constpart) == 1


def _fix_slice_binop_bound(node, ctx):
    return [_k_param_name(node, ctx)]


def _match_slice_hardcoded(node, ctx):
    if not (isinstance(node, ast.Constant) and isinstance(node.value, int) and node.value >= 0):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Slice) or parent.upper is not node:
        return False
    if parent.lower is not None or parent.step is not None:
        return False
    return _k_param_name(node, ctx) is not None


def _fix_slice_hardcoded(node, ctx):
    return [_k_param_name(node, ctx)]


# ---------- 7/8: loop condition off-by-one against k ----------

def _match_lte_k_while(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.While) or parent.test is not node:
        return False
    kname = _k_param_name(node, ctx)
    right = node.comparators[0]
    return kname is not None and isinstance(right, ast.Name) and right.id == kname


def _fix_lte_k_while(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _match_gte_zero_k_while(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.While) or parent.test is not node:
        return False
    kname = _k_param_name(node, ctx)
    left, right = node.left, node.comparators[0]
    if kname is None or not (isinstance(left, ast.Name) and left.id == kname):
        return False
    return isinstance(right, ast.Constant) and right.value == 0


def _fix_gte_zero_k_while(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


# ---------- 9: missing return of accumulator ----------

def _match_missing_return(node, ctx):
    fn = ctx.parent(node)
    if not isinstance(fn, ast.FunctionDef) or not fn.body or fn.body[-1] is not node:
        return False
    if isinstance(node, ast.Return):
        return False
    if _contains_return(fn):
        return False
    return _find_empty_list_acc(fn) is not None


def _fix_missing_return(node, ctx):
    fn = ctx.parent(node)
    acc = _find_empty_list_acc(fn)
    return [ctx.text(node) + "\nreturn " + acc]


# ---------- 10: append(x.remove(y)) instead of append(y); x.remove(y) ----------

def _match_append_of_remove(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    call = node.value
    if not (_is_call_attr(call, "append") and len(call.args) == 1):
        return False
    inner = call.args[0]
    return _is_call_attr(inner, "remove") and len(inner.args) == 1


def _fix_append_of_remove(node, ctx):
    call = node.value
    inner = call.args[0]
    append_recv = ctx.text(call.func.value)
    remove_recv = ctx.text(inner.func.value)
    val = ctx.text(inner.args[0])
    return [f"{append_recv}.append({val})\n{remove_recv}.remove({val})"]


# ---------- 11: returning the original list instead of the accumulator ----------

def _match_return_wrong_list(node, ctx):
    if not isinstance(node, ast.Return) or not isinstance(node.value, ast.Subscript):
        return False
    if not isinstance(node.value.value, ast.Name):
        return False
    fn = _enclosing_function(node, ctx)
    if fn is None or not fn.args.args:
        return False
    first_param = fn.args.args[0].arg
    if node.value.value.id != first_param:
        return False
    acc = _find_empty_list_acc(fn)
    return acc is not None and acc != first_param


def _fix_return_wrong_list(node, ctx):
    fn = _enclosing_function(node, ctx)
    acc = _find_empty_list_acc(fn)
    slice_text = ctx.text(node.value.slice)
    return [f"{acc}[{slice_text}]"]


# ---------- 12/13: range(k-1) / range(..., -1) off-by-one ----------

def _match_range_k_minus1(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Sub)):
        return False
    kname = _k_param_name(node, ctx)
    if kname is None:
        return False
    return (isinstance(arg.left, ast.Name) and arg.left.id == kname
            and isinstance(arg.right, ast.Constant) and arg.right.value == 1)


def _fix_range_k_minus1(node, ctx):
    return [f"range({_k_param_name(node, ctx)})"]


def _match_range_neg1_end(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"):
        return False
    if len(node.args) != 2:
        return False
    second = node.args[1]
    return (isinstance(second, ast.UnaryOp) and isinstance(second.op, ast.USub)
            and isinstance(second.operand, ast.Constant) and second.operand.value == 1)


def _fix_range_neg1_end(node, ctx):
    return [f"range({ctx.text(node.args[0])}, 0)"]


# ---------- 14: pop(value) instead of pop(index) ----------

def _match_pop_value_not_index(node, ctx):
    if not (isinstance(node, ast.Call) and _is_call_attr(node, "pop")):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    return isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == "max"


def _fix_pop_value_not_index(node, ctx):
    recv = ctx.text(node.func.value)
    arg_text = ctx.text(node.args[0])
    return [f"{recv}.pop({recv}.index({arg_text}))"]


# ---------- 15: list.append[x] / list.remove[x] typo for calls ----------

def _match_bracket_call(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    val = node.value
    return isinstance(val, ast.Attribute) and val.attr in ("append", "remove")


def _fix_bracket_call(node, ctx):
    idx_text = ctx.text(_slice_expr(node.slice))
    return [ctx.text(node.value) + "(" + idx_text + ")"]


# ---------- 16: fake swap without tuple assignment ----------

def _match_fake_swap_first(node, ctx):
    if not isinstance(node, ast.Assign) or len(node.targets) != 1:
        return False
    target = node.targets[0]
    value = node.value
    if not (isinstance(target, ast.Subscript) and isinstance(value, ast.Subscript)):
        return False
    body, idx = _get_siblings(node, ctx)
    if body is None or idx + 1 >= len(body):
        return False
    nxt = body[idx + 1]
    if not (isinstance(nxt, ast.Assign) and len(nxt.targets) == 1):
        return False
    t2, v2 = nxt.targets[0], nxt.value
    if not (isinstance(t2, ast.Subscript) and isinstance(v2, ast.Subscript)):
        return False
    return ast.dump(t2) == ast.dump(value) and ast.dump(v2) == ast.dump(target)


def _fix_fake_swap_first(node, ctx):
    target, value = node.targets[0], node.value
    return [f"{ctx.text(target)}, {ctx.text(value)} = {ctx.text(value)}, {ctx.text(target)}"]


def _match_fake_swap_second(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    body, idx = _get_siblings(node, ctx)
    if body is None or idx == 0:
        return False
    return _match_fake_swap_first(body[idx - 1], ctx)


def _fix_fake_swap_second(node, ctx):
    return [""]


# ---------- 17: range(len(x)) index used without subscripting ----------

def _match_missing_index_subscript(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    parent_if = ctx.parent(node)
    if not isinstance(parent_if, ast.If) or parent_if.test is not node:
        return False
    forn = _enclosing_for(parent_if, ctx)
    if forn is None or not isinstance(forn.target, ast.Name):
        return False
    it = forn.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"):
        return False
    if len(it.args) != 1:
        return False
    lenarg = it.args[0]
    if not (isinstance(lenarg, ast.Call) and isinstance(lenarg.func, ast.Name) and lenarg.func.id == "len"):
        return False
    if len(lenarg.args) != 1 or not isinstance(lenarg.args[0], ast.Name):
        return False
    left = node.left
    return isinstance(left, ast.Name) and left.id == forn.target.id


def _fix_missing_index_subscript(node, ctx):
    parent_if = ctx.parent(node)
    forn = _enclosing_for(parent_if, ctx)
    lenarg = forn.iter.args[0]
    list_name = lenarg.args[0].id
    loop_var_text = ctx.text(node.left)
    right_text = ctx.text(node.comparators[0])
    return [f"{list_name}[{loop_var_text}] == {right_text}"]


# ---------- 18: single-pass bubble sort needs an outer pass ----------

def _match_single_pass_bubble(node, ctx):
    if not isinstance(node, ast.For):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if not isinstance(node.target, ast.Name):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.If):
        return False
    ifstmt = node.body[0]
    if len(ifstmt.body) != 1 or not isinstance(ifstmt.body[0], ast.Assign):
        return False
    return isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == "range"


def _fix_single_pass_bubble(node, ctx):
    outer_var = "_pass_i" if node.target.id != "_pass_i" else "_pass_j"
    rng = node.iter
    length_expr = None
    if rng.args and isinstance(rng.args[0], ast.BinOp):
        length_expr = ctx.text(rng.args[0].left)
    if length_expr is None:
        length_expr = "len(" + ctx.text(node.target) + ")"
    inner_text = ctx.text(node)
    indented = "\n".join("    " + line for line in inner_text.split("\n"))
    return [f"for {outer_var} in range({length_expr}):\n{indented}"]


# ---------- 19/20: seed `x = y[0]` wrongly placed at end of a while body ----------

def _match_reseed_delete(node, ctx):
    parent = ctx.parent(node)
    return isinstance(parent, ast.While) and _find_reseed(parent) is node


def _fix_reseed_delete(node, ctx):
    return [""]


def _match_reseed_prepend(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.While):
        return False
    reseed = _find_reseed(parent)
    if reseed is None or reseed is node:
        return False
    return parent.body[0] is node


def _fix_reseed_prepend(node, ctx):
    parent = ctx.parent(node)
    reseed = _find_reseed(parent)
    return [ctx.text(reseed) + "\n" + ctx.text(node)]


# ---------- 21: elif k == 0 returns the wrong (non-empty) value ----------

def _match_wrong_k0_return(node, ctx):
    if not isinstance(node, ast.Return):
        return False
    parent_if = ctx.parent(node)
    if not isinstance(parent_if, ast.If) or node not in parent_if.body:
        return False
    test = parent_if.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.Eq)):
        return False
    right = test.comparators[0]
    if not (isinstance(right, ast.Constant) and right.value == 0):
        return False
    left = test.left
    kname = _k_param_name(node, ctx)
    if kname is None or not (isinstance(left, ast.Name) and left.id == kname):
        return False
    if isinstance(node.value, ast.List) and len(node.value.elts) == 0:
        return False
    return True


def _fix_wrong_k0_return(node, ctx):
    return ["return []"]


# ---------- 22: missing k == 0 guard at top of function ----------

def _match_missing_k0_guard(node, ctx):
    fn = ctx.parent(node)
    if not isinstance(fn, ast.FunctionDef) or not fn.body or fn.body[0] is not node:
        return False
    if isinstance(node, (ast.If,)):
        return False
    kname = _k_param_name(node, ctx)
    if kname is None:
        return False
    for n in _walk_no_nested_func(fn):
        if isinstance(n, ast.Compare):
            left = n.left
            for comp in n.comparators:
                if (isinstance(comp, ast.Constant) and comp.value == 0
                        and isinstance(left, ast.Name) and left.id == kname):
                    return False
    return True


def _fix_missing_k0_guard(node, ctx):
    kname = _k_param_name(node, ctx)
    return [f"if {kname} == 0:\n    return []\n" + ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="remove_before_append_delete", match=_match_remove_before_append,
                    replace=_fix_remove_before_append_delete, symptoms=("wrong",)),
            Rewrite(name="append_after_remove_reorder", match=_match_append_after_remove,
                    replace=_fix_append_after_remove, symptoms=("wrong",)),
            Rewrite(name="max_track_wrong_assign_target", match=_match_max_track_wrong_target,
                    replace=_fix_max_track_wrong_target, symptoms=("wrong",)),
            Rewrite(name="append_uses_wrong_var", match=_match_append_wrong_var,
                    replace=_fix_append_wrong_var, symptoms=("wrong", "err:NameError")),
            Rewrite(name="slice_binop_off_by_one", match=_match_slice_binop_bound,
                    replace=_fix_slice_binop_bound, symptoms=("wrong",)),
            Rewrite(name="slice_hardcoded_bound", match=_match_slice_hardcoded,
                    replace=_fix_slice_hardcoded, symptoms=("wrong",)),
            Rewrite(name="while_lte_k_should_be_lt", match=_match_lte_k_while,
                    replace=_fix_lte_k_while, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="while_gte_zero_k_should_be_gt", match=_match_gte_zero_k_while,
                    replace=_fix_gte_zero_k_while, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="missing_return_accumulator", match=_match_missing_return,
                    replace=_fix_missing_return, symptoms=("wrong",)),
            Rewrite(name="append_of_remove_call", match=_match_append_of_remove,
                    replace=_fix_append_of_remove, symptoms=("wrong", "timeout")),
            Rewrite(name="return_wrong_list_variable", match=_match_return_wrong_list,
                    replace=_fix_return_wrong_list, symptoms=("wrong",)),
            Rewrite(name="range_k_minus1_off_by_one", match=_match_range_k_minus1,
                    replace=_fix_range_k_minus1, symptoms=("wrong",)),
            Rewrite(name="range_neg1_end_off_by_one", match=_match_range_neg1_end,
                    replace=_fix_range_neg1_end, symptoms=("wrong", "timeout")),
            Rewrite(name="pop_value_should_be_index", match=_match_pop_value_not_index,
                    replace=_fix_pop_value_not_index, symptoms=("wrong", "err:ValueError")),
            Rewrite(name="bracket_instead_of_call", match=_match_bracket_call,
                    replace=_fix_bracket_call, symptoms=("err:TypeError",)),
            Rewrite(name="fake_swap_first", match=_match_fake_swap_first,
                    replace=_fix_fake_swap_first, symptoms=("wrong",)),
            Rewrite(name="fake_swap_second_delete", match=_match_fake_swap_second,
                    replace=_fix_fake_swap_second, symptoms=("wrong",)),
            Rewrite(name="missing_index_subscript", match=_match_missing_index_subscript,
                    replace=_fix_missing_index_subscript, symptoms=("wrong",)),
            Rewrite(name="single_pass_bubble_needs_outer_loop", match=_match_single_pass_bubble,
                    replace=_fix_single_pass_bubble, symptoms=("wrong",)),
            Rewrite(name="reseed_at_end_delete", match=_match_reseed_delete,
                    replace=_fix_reseed_delete, symptoms=("err:IndexError",)),
            Rewrite(name="reseed_at_end_prepend", match=_match_reseed_prepend,
                    replace=_fix_reseed_prepend, symptoms=("err:IndexError",)),
            Rewrite(name="wrong_k0_return_value", match=_match_wrong_k0_return,
                    replace=_fix_wrong_k0_return, symptoms=("wrong",)),
            Rewrite(name="missing_k0_guard", match=_match_missing_k0_guard,
                    replace=_fix_missing_k0_guard, symptoms=("wrong", "err:IndexError")),
        ]