from src.core.repair import Rule
import ast
import builtins as _builtins
from src.core.rewrite import Rewrite

BUILTIN_NAMES = set(dir(_builtins))


def _ancestors(node, ctx):
    cur = node
    while True:
        par = ctx.parent(cur)
        if par is None:
            return
        yield par
        cur = par


def _enclosing_function(node, ctx):
    for anc in _ancestors(node, ctx):
        if isinstance(anc, ast.FunctionDef):
            return anc
    return None


def _enclosing_for(node, ctx):
    for anc in _ancestors(node, ctx):
        if isinstance(anc, ast.For):
            return anc
        if isinstance(anc, ast.FunctionDef):
            return None
    return None


def _module_function_names(ctx):
    try:
        return {n.name for n in ast.walk(ctx.tree) if isinstance(n, ast.FunctionDef)}
    except Exception:
        return set()


def _assigned_names(func):
    names = set()
    try:
        for a in func.args.args:
            names.add(a.arg)
    except Exception:
        pass
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    names.add(t.id)
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
        if isinstance(n, ast.FunctionDef):
            for a in n.args.args:
                names.add(a.arg)
        if isinstance(n, ast.Lambda):
            for a in n.args.args:
                names.add(a.arg)
        if isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            for gen in n.generators:
                if isinstance(gen.target, ast.Name):
                    names.add(gen.target.id)
        if isinstance(n, ast.ExceptHandler) and n.name:
            names.add(n.name)
    return names


def _declared_empty_list(func):
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.List) and len(n.value.elts) == 0):
            return n.targets[0].id
    return None


def _levenshtein(a, b):
    if a == b:
        return 0
    la, lb = len(a), len(b)
    dp = list(range(lb + 1))
    for i in range(1, la + 1):
        prev = dp[0]
        dp[0] = i
        for j in range(1, lb + 1):
            cur = dp[j]
            dp[j] = min(dp[j] + 1, dp[j - 1] + 1, prev + (a[i - 1] != b[j - 1]))
            prev = cur
    return dp[lb]


def _base_name_id(expr):
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Subscript) and isinstance(expr.value, ast.Name):
        return expr.value.id
    return None


def _compare_sides(test):
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and len(test.comparators) == 1):
        return None
    lid = _base_name_id(test.left)
    rid = _base_name_id(test.comparators[0])
    if lid is None or rid is None:
        return None
    return (lid, rid)


def _tracking_var(for_node):
    if not isinstance(for_node.target, ast.Name):
        return None
    loopvar = for_node.target.id
    for stmt in for_node.body:
        if isinstance(stmt, ast.If):
            for s in stmt.body:
                if (isinstance(s, ast.Assign) and len(s.targets) == 1
                        and isinstance(s.targets[0], ast.Name)
                        and isinstance(s.value, ast.Name) and s.value.id == loopvar):
                    return (loopvar, s.targets[0].id)
    return None


def _enclosing_stmt(node, ctx):
    cur = node
    while not isinstance(cur, ast.stmt):
        par = ctx.parent(cur)
        if par is None:
            return None
        cur = par
    return cur


def _find_block(stmt, ctx):
    parent = ctx.parent(stmt)
    field = ctx.field(stmt)
    if parent is None or field is None:
        return None
    body = getattr(parent, field, None)
    if not isinstance(body, list):
        return None
    try:
        idx = body.index(stmt)
    except ValueError:
        return None
    return (body, idx)


def _nearest_preceding_for(body, idx):
    for j in range(idx - 1, -1, -1):
        if isinstance(body[j], ast.For):
            return body[j]
    return None


# ---------------------------------------------------------------- rule 1
def _is_missing_return_tail(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if ctx.field(node) != 'body':
        return False
    if not parent.body or parent.body[-1] is not node:
        return False
    if isinstance(node, ast.Return):
        return False
    for n in ast.walk(parent):
        if isinstance(n, ast.Return):
            return False
    return True


def _missing_return_tail_fix(node, ctx):
    parent = ctx.parent(node)
    name = _declared_empty_list(parent)
    if name is None:
        return []
    return [ctx.text(node) + "\nreturn " + name]


# ---------------------------------------------------------------- rule 2
def _is_print_stmt(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name) and node.value.func.id == 'print'
            and len(node.value.args) == 1 and not node.value.keywords)


def _print_to_return(node, ctx):
    return ["return " + ctx.text(node.value.args[0])]


# ---------------------------------------------------------------- rule 3
def _is_bare_reverse_stmt(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Attribute)
            and node.value.attr == 'reverse')


def _bare_reverse_stmt_fix(node, ctx):
    base = node.value.value
    out = ["", ctx.text(base) + ".reverse()"]
    if isinstance(base, ast.Call) and len(base.args) == 1 and isinstance(base.args[0], ast.Name):
        out.append(ctx.text(base) + "\n" + base.args[0].id + ".reverse()")
    return out


# ---------------------------------------------------------------- rule 4
def _is_return_bare_reverse(node, ctx):
    return (isinstance(node, ast.Return) and node.value is not None
            and isinstance(node.value, ast.Attribute) and node.value.attr == 'reverse')


def _return_bare_reverse_fix(node, ctx):
    base = ctx.text(node.value.value)
    return ["return " + base, base + ".reverse()\nreturn " + base]


# ---------------------------------------------------------------- rule 5
def _is_return_call_reverse(node, ctx):
    return (isinstance(node, ast.Return) and node.value is not None
            and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == 'reverse')


def _return_call_reverse_fix(node, ctx):
    base = ctx.text(node.value.func.value)
    return [base + ".reverse()\nreturn " + base]


# ---------------------------------------------------------------- rule 6
def _is_return_name_bare_reverse_elsewhere(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    target_id = node.value.id
    for n in ast.walk(func):
        if (isinstance(n, ast.Expr) and isinstance(n.value, ast.Attribute)
                and n.value.attr == 'reverse' and isinstance(n.value.value, ast.Name)
                and n.value.value.id == target_id):
            return True
    return False


def _return_name_bare_reverse_fix(node, ctx):
    name = node.value.id
    return [name + ".reverse()\nreturn " + name]


# ---------------------------------------------------------------- rule 7
def _is_wrong_accum_name(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Call) and len(parent.args) == 1 and parent.args[0] is node
            and isinstance(parent.func, ast.Attribute) and parent.func.attr in ('remove', 'append')):
        return False
    stmt = _enclosing_stmt(node, ctx)
    if stmt is None:
        return False
    blk = _find_block(stmt, ctx)
    if blk is None:
        return False
    body, idx = blk
    for_node = _nearest_preceding_for(body, idx)
    if for_node is None:
        return False
    tv = _tracking_var(for_node)
    if tv is None:
        return False
    loopvar, trackvar = tv
    return node.id == loopvar and node.id != trackvar


def _wrong_accum_name_fix(node, ctx):
    stmt = _enclosing_stmt(node, ctx)
    body, idx = _find_block(stmt, ctx)
    for_node = _nearest_preceding_for(body, idx)
    _, trackvar = _tracking_var(for_node)
    return [trackvar]


# ---------------------------------------------------------------- rule 8
def _is_undefined_append_target(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'append' and isinstance(node.func.value, ast.Name)):
        return False
    name = node.func.value.id
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    if name in _assigned_names(func):
        return False
    return True


def _undefined_append_target_fix(node, ctx):
    func = _enclosing_function(node, ctx)
    declared = _declared_empty_list(func)
    if declared is None:
        return []
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [declared + ".append(" + args_text + ")"]


# ---------------------------------------------------------------- rule 9
def _is_undefined_return_name(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    return node.value.id not in _assigned_names(func)


def _undefined_return_name_fix(node, ctx):
    func = _enclosing_function(node, ctx)
    declared = _declared_empty_list(func)
    if declared is None:
        return []
    return ["return " + declared]


# ---------------------------------------------------------------- rule 10
def _is_undefined_remove_target(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'remove' and isinstance(node.func.value, ast.Name)):
        return False
    name = node.func.value.id
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    return name not in _assigned_names(func)


def _undefined_remove_target_fix(node, ctx):
    func = _enclosing_function(node, ctx)
    if not func.args.args:
        return []
    param0 = func.args.args[0].arg
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [param0 + ".remove(" + args_text + ")"]


# ---------------------------------------------------------------- rule 11
def _is_undefined_while_test_name(node, ctx):
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.While) and parent.test is node and isinstance(node, ast.Name)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    return node.id not in _assigned_names(func)


def _undefined_while_test_name_fix(node, ctx):
    func = _enclosing_function(node, ctx)
    if not func.args.args:
        return []
    return [func.args.args[0].arg]


# ---------------------------------------------------------------- rule 12
def _is_typo_track_assign_value(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Assign) and len(parent.targets) == 1
            and isinstance(parent.targets[0], ast.Name) and parent.value is node):
        return False
    gp = ctx.parent(parent)
    if not isinstance(gp, ast.If):
        return False
    sides = _compare_sides(gp.test)
    if sides is None:
        return False
    lid, rid = sides
    tname = parent.targets[0].id
    if tname == lid:
        other = rid
    elif tname == rid:
        other = lid
    else:
        return False
    return node.id != other


def _typo_track_assign_value_fix(node, ctx):
    parent = ctx.parent(node)
    gp = ctx.parent(parent)
    lid, rid = _compare_sides(gp.test)
    tname = parent.targets[0].id
    other = rid if tname == lid else lid
    return [other]


# ---------------------------------------------------------------- rule 13
def _is_flipped_tracking_assign(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name) and isinstance(node.value, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and len(parent.body) == 1 and parent.body[0] is node):
        return False
    for_node = ctx.parent(parent)
    if not (isinstance(for_node, ast.For) and isinstance(for_node.target, ast.Name)):
        return False
    if parent not in for_node.body:
        return False
    sides = _compare_sides(parent.test)
    if sides is None:
        return False
    lid, rid = sides
    loopvar = for_node.target.id
    tname = node.targets[0].id
    if tname != loopvar:
        return False
    other = rid if lid == loopvar else lid
    return node.value.id == other


def _flipped_tracking_assign_fix(node, ctx):
    tname = node.targets[0].id
    vname = node.value.id
    return [vname + " = " + tname]


# ---------------------------------------------------------------- rule 14
def _is_simple_compare(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE)))


def _compare_operator_variants(node, ctx):
    sym_of = {ast.Lt: '<', ast.Gt: '>', ast.LtE: '<=', ast.GtE: '>='}
    cur = sym_of[type(node.ops[0])]
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    return [left + " " + sym + " " + right for sym in ('<', '>', '<=', '>=') if sym != cur]


# ---------------------------------------------------------------- rule 15
def _is_range_call(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'range' and len(node.args) in (1, 2))


def _range_candidates(node, ctx):
    args = node.args
    texts = [ctx.text(a) for a in args]
    cands = set()
    last = args[-1]
    if isinstance(last, ast.BinOp) and isinstance(last.op, ast.Add):
        new_last = ctx.text(last.left)
        new_args = texts[:-1] + [new_last]
        cands.add("range(" + ", ".join(new_args) + ")")
    if len(args) == 2 and isinstance(args[0], ast.Constant) and args[0].value == 1:
        cands.add("range(0, " + texts[1] + ")")
        cands.add("range(" + texts[1] + ")")
        if isinstance(args[1], ast.BinOp) and isinstance(args[1].op, ast.Add):
            inner = ctx.text(args[1].left)
            cands.add("range(0, " + inner + ")")
            cands.add("range(" + inner + ")")
    cands.discard(ctx.text(node))
    return list(cands)


# ---------------------------------------------------------------- rule 16
def _is_self_assign_append(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    val = node.value
    if not (isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute)
            and val.func.attr == 'append' and isinstance(val.func.value, ast.Name)):
        return False
    return val.func.value.id == node.targets[0].id


def _self_assign_append_fix(node, ctx):
    return [ctx.text(node.value)]


# ---------------------------------------------------------------- rule 17
def _is_bare_max_call(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'max' and len(node.args) == 1 and not node.keywords):
        return False
    if not isinstance(node.args[0], ast.Name):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or not func.args.args:
        return False
    return node.args[0].id == func.args.args[0].arg


def _bare_max_fix(node, ctx):
    arg = ctx.text(node.args[0])
    return ["max(" + arg + ", key=lambda p: p[1])"]


# ---------------------------------------------------------------- rule 18
def _is_pop_no_args_in_merge(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'pop' and not node.args):
        return False
    for anc in _ancestors(node, ctx):
        if isinstance(anc, ast.While):
            t = anc.test
            return isinstance(t, ast.BoolOp) and isinstance(t.op, ast.And)
        if isinstance(anc, ast.FunctionDef):
            return False
    return False


def _pop_no_args_fix(node, ctx):
    return [ctx.text(node.func) + "(0)"]


# ---------------------------------------------------------------- rule 19
def _is_pop_subscript_misuse(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr == 'pop')


def _pop_subscript_fix(node, ctx):
    base = ctx.text(node.value)
    idx = ctx.text(node.slice)
    return [base + "(" + idx + ")"]


# ---------------------------------------------------------------- rule 20
def _is_broken_swap(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1):
        return False
    tgt = node.targets[0]
    val = node.value
    if not (isinstance(tgt, ast.Tuple) and isinstance(val, ast.Tuple)
            and len(tgt.elts) == 2 and len(val.elts) == 2):
        return False
    return ctx.text(val.elts[0]) == ctx.text(val.elts[1])


def _broken_swap_fix(node, ctx):
    tgt = node.targets[0]
    t0, t1 = ctx.text(tgt.elts[0]), ctx.text(tgt.elts[1])
    return [t0 + ", " + t1 + " = " + t1 + ", " + t0]


# ---------------------------------------------------------------- rule 21
def _is_bare_tuple_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1):
        return False
    l, r = node.left, node.comparators[0]
    if not (isinstance(l, ast.Name) and isinstance(r, ast.Name)):
        return False
    for_node = _enclosing_for(node, ctx)
    if for_node is None or not isinstance(for_node.target, ast.Name):
        return False
    loopvar = for_node.target.id
    return l.id == loopvar or r.id == loopvar


def _bare_tuple_compare_fix(node, ctx):
    op_map = {ast.Lt: '<', ast.Gt: '>', ast.LtE: '<=', ast.GtE: '>='}
    sym = op_map.get(type(node.ops[0]))
    if sym is None:
        return []
    l = ctx.text(node.left) + "[1]"
    r = ctx.text(node.comparators[0]) + "[1]"
    return [l + " " + sym + " " + r]


# ---------------------------------------------------------------- rule 22
def _is_return_list_reverse_call(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == 'reverse'
            and isinstance(node.value.func.value, ast.Name) and node.value.func.value.id == 'list'
            and len(node.value.args) == 1)


def _return_list_reverse_call_fix(node, ctx):
    arg = ctx.text(node.value.args[0])
    return ["return " + arg + "[::-1]"]


# ---------------------------------------------------------------- rule 23
def _is_reverse_call_with_args(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'reverse' and len(node.args) > 0)


def _reverse_call_with_args_fix(node, ctx):
    return [ctx.text(node.func) + "()"]


# ---------------------------------------------------------------- rule 24
def _is_typo_name(node, ctx):
    if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
        return False
    if node.id in BUILTIN_NAMES:
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    if node.id in _module_function_names(ctx):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    names = _assigned_names(func)
    if node.id in names:
        return False
    cands = [n for n in names if n and n[0] == node.id[0] and _levenshtein(n, node.id) <= 2]
    return len(cands) > 0


def _typo_name_fix(node, ctx):
    func = _enclosing_function(node, ctx)
    names = _assigned_names(func)
    cands = [n for n in names if n and n[0] == node.id[0] and _levenshtein(n, node.id) <= 2]
    cands.sort(key=lambda n: _levenshtein(n, node.id))
    return cands[:3]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="missing_return_tail", match=_is_missing_return_tail,
                    replace=_missing_return_tail_fix, symptoms=("wrong",)),
            Rewrite(name="print_to_return", match=_is_print_stmt,
                    replace=_print_to_return, symptoms=("wrong",)),
            Rewrite(name="bare_reverse_stmt", match=_is_bare_reverse_stmt,
                    replace=_bare_reverse_stmt_fix, symptoms=("wrong",)),
            Rewrite(name="return_bare_reverse", match=_is_return_bare_reverse,
                    replace=_return_bare_reverse_fix, symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="return_call_reverse_split", match=_is_return_call_reverse,
                    replace=_return_call_reverse_fix, symptoms=("wrong",)),
            Rewrite(name="return_name_insert_reverse", match=_is_return_name_bare_reverse_elsewhere,
                    replace=_return_name_bare_reverse_fix, symptoms=("wrong",)),
            Rewrite(name="wrong_accum_name", match=_is_wrong_accum_name,
                    replace=_wrong_accum_name_fix, symptoms=("wrong",)),
            Rewrite(name="undefined_append_target", match=_is_undefined_append_target,
                    replace=_undefined_append_target_fix, symptoms=("err:NameError", "wrong")),
            Rewrite(name="undefined_return_name", match=_is_undefined_return_name,
                    replace=_undefined_return_name_fix, symptoms=("err:NameError", "wrong")),
            Rewrite(name="undefined_remove_target", match=_is_undefined_remove_target,
                    replace=_undefined_remove_target_fix, symptoms=("err:NameError", "wrong")),
            Rewrite(name="undefined_while_test_name", match=_is_undefined_while_test_name,
                    replace=_undefined_while_test_name_fix, symptoms=("err:NameError", "wrong")),
            Rewrite(name="typo_track_assign_value", match=_is_typo_track_assign_value,
                    replace=_typo_track_assign_value_fix, symptoms=("err:NameError", "wrong")),
            Rewrite(name="flipped_tracking_assign", match=_is_flipped_tracking_assign,
                    replace=_flipped_tracking_assign_fix, symptoms=("wrong",)),
            Rewrite(name="compare_operator_variants", match=_is_simple_compare,
                    replace=_compare_operator_variants, symptoms=("wrong",)),
            Rewrite(name="range_offbyone", match=_is_range_call,
                    replace=_range_candidates, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="self_assign_append", match=_is_self_assign_append,
                    replace=_self_assign_append_fix, symptoms=("wrong",)),
            Rewrite(name="bare_max_add_key", match=_is_bare_max_call,
                    replace=_bare_max_fix, symptoms=("wrong",)),
            Rewrite(name="pop_no_args_in_merge", match=_is_pop_no_args_in_merge,
                    replace=_pop_no_args_fix, symptoms=("wrong",)),
            Rewrite(name="pop_subscript_to_call", match=_is_pop_subscript_misuse,
                    replace=_pop_subscript_fix, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="broken_tuple_swap", match=_is_broken_swap,
                    replace=_broken_swap_fix, symptoms=("wrong",)),
            Rewrite(name="bare_tuple_compare_add_index", match=_is_bare_tuple_compare,
                    replace=_bare_tuple_compare_fix, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="return_list_reverse_call", match=_is_return_list_reverse_call,
                    replace=_return_list_reverse_call_fix, symptoms=("wrong",)),
            Rewrite(name="reverse_call_with_args", match=_is_reverse_call_with_args,
                    replace=_reverse_call_with_args_fix, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="typo_name_generic", match=_is_typo_name,
                    replace=_typo_name_fix, symptoms=("err:NameError", "wrong")),
        ]