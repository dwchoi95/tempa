from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def enclosing_function(node, ctx):
    n = node
    while True:
        n = ctx.parent(n)
        if n is None or isinstance(n, ast.FunctionDef):
            return n


def enclosing_for(node, ctx):
    cur = node
    while True:
        cur = ctx.parent(cur)
        if cur is None or isinstance(cur, ast.FunctionDef):
            return None
        if isinstance(cur, ast.For):
            return cur


def find_accumulators(func):
    if func is None:
        return None, None
    candidates = []
    for stmt in func.body:
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and isinstance(stmt.value, (ast.List, ast.Tuple))
                and len(stmt.value.elts) == 0):
            candidates.append((stmt.targets[0].id, type(stmt.value).__name__))
    for name, kind in candidates:
        for n in ast.walk(func):
            if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                    and n.func.attr in ("append", "extend", "insert")
                    and isinstance(n.func.value, ast.Name) and n.func.value.id == name):
                return name, kind
            if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and n.target.id == name:
                return name, kind
    if candidates:
        return candidates[0]
    return None, None


def find_append_target(for_node):
    if for_node is None:
        return None
    for n in ast.walk(for_node):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr in ("append", "extend", "insert")
                and isinstance(n.func.value, ast.Name)):
            return n.func.value.id
    return None


def is_undefined_in_func(name, func):
    if any(a.arg == name for a in func.args.args):
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name) and t.id == name:
                    return False
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and n.target.id == name:
            return False
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name) and n.target.id == name:
            return False
    return True


def _get_subscript_index(node):
    sl = node.slice
    if hasattr(ast, "Index") and isinstance(sl, ast.Index):
        return sl.value
    return sl


def _match_iter_over_list(node, ctx):
    return (isinstance(node, ast.Name) and node.id == "list"
            and isinstance(ctx.parent(node), ast.For) and ctx.field(node) == "iter")


def _fix_iter_over_list(node, ctx):
    func = enclosing_function(node, ctx)
    if not func or not func.args.args:
        return []
    param = func.args.args[0].arg
    if param == "list":
        return []
    return [param]


def _match_membership_wrong(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], (ast.In, ast.NotIn))):
        return False
    comp = node.comparators[0]
    if not isinstance(comp, ast.Name):
        return False
    efor = enclosing_for(node, ctx)
    if efor is None:
        return False
    iter_name = efor.iter.id if isinstance(efor.iter, ast.Name) else None
    if comp.id != iter_name and comp.id != "list":
        return False
    func = enclosing_function(node, ctx)
    acc, _ = find_accumulators(func)
    if not acc:
        acc = find_append_target(efor)
    if not acc or acc == comp.id:
        return False
    return True


def _fix_membership_wrong(node, ctx):
    func = enclosing_function(node, ctx)
    acc, _ = find_accumulators(func)
    if not acc:
        acc = find_append_target(enclosing_for(node, ctx))
    op_text = " not in " if isinstance(node.ops[0], ast.NotIn) else " in "
    return [ctx.text(node.left) + op_text + acc]


def _match_append_undefined(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Attribute) and ctx.field(node) == "value"):
        return False
    if parent.attr not in ("append", "extend", "insert"):
        return False
    func = enclosing_function(node, ctx)
    if not func:
        return False
    if not is_undefined_in_func(node.id, func):
        return False
    acc, _ = find_accumulators(func)
    if not acc or acc == node.id:
        return False
    return True


def _fix_append_undefined(node, ctx):
    func = enclosing_function(node, ctx)
    acc, _ = find_accumulators(func)
    return [acc]


def _match_return_wrong(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = enclosing_function(node, ctx)
    acc, _ = find_accumulators(func)
    if not acc:
        return False
    return node.value.id != acc


def _fix_return_wrong(node, ctx):
    func = enclosing_function(node, ctx)
    acc, _ = find_accumulators(func)
    return ["return " + acc]


def _match_missing_parens(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Attribute)


def _fix_missing_parens(node, ctx):
    return [ctx.text(node.value) + "()"]


def _match_missing_return(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if not parent.body or parent.body[-1] is not node:
        return False
    if isinstance(node, ast.Return):
        return False
    if any(isinstance(n, ast.Return) for n in ast.walk(parent)):
        return False
    acc, _ = find_accumulators(parent)
    return acc is not None


def _fix_missing_return(node, ctx):
    parent = ctx.parent(node)
    acc, _ = find_accumulators(parent)
    return [ctx.text(node) + "\nreturn " + acc]


def _match_in_should_be_notin(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.In)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    acc = node.comparators[0]
    if not isinstance(acc, ast.Name):
        return False
    for n in ast.walk(parent):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == "append" and isinstance(n.func.value, ast.Name)
                and n.func.value.id == acc.id):
            return True
    return False


def _fix_in_should_be_notin(node, ctx):
    return [ctx.text(node.left) + " not in " + ctx.text(node.comparators[0])]


def _match_lists_typo(node, ctx):
    if not (isinstance(node, ast.Name) and node.id == "lists"):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Call) and parent.func is node and len(parent.args) == 1):
        return False
    a = parent.args[0]
    return (isinstance(a, ast.Call) and isinstance(a.func, ast.Attribute) and a.func.attr == "fromkeys")


def _fix_lists_typo(node, ctx):
    return ["list"]


def _match_return_fromkeys_bare(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "fromkeys")


def _fix_return_fromkeys_bare(node, ctx):
    return ["return list(" + ctx.text(node.value) + ")"]


def _match_augassign_wrap(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)
            and isinstance(node.target, ast.Name)):
        return False
    if isinstance(node.value, (ast.List, ast.Tuple)):
        return False
    func = enclosing_function(node, ctx)
    acc, kind = find_accumulators(func)
    if not acc or acc != node.target.id:
        return False
    return kind in ("List", "Tuple")


def _fix_augassign_wrap(node, ctx):
    func = enclosing_function(node, ctx)
    acc, kind = find_accumulators(func)
    val_text = ctx.text(node.value)
    new_val = "[" + val_text + "]" if kind == "List" else "(" + val_text + ",)"
    return [ctx.text(node.target) + " += " + new_val]


def _get_body_list(node, ctx):
    parent = ctx.parent(node)
    if parent is None:
        return None, None
    for field in ("body", "orelse", "finalbody"):
        lst = getattr(parent, field, None)
        if isinstance(lst, list) and node in lst:
            return lst, parent
    return None, None


def _is_reassign_if(node, ctx):
    if not isinstance(node, ast.If) or node.orelse or len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)):
        return False
    val = stmt.value
    if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
        return False
    body_list, _ = _get_body_list(node, ctx)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx + 1 >= len(body_list):
        return False
    nxt = body_list[idx + 1]
    return (isinstance(nxt, ast.AugAssign) and isinstance(nxt.op, ast.Add) and isinstance(nxt.target, ast.Name))


def _fix_reassign_if(node, ctx):
    body_list, _ = _get_body_list(node, ctx)
    idx = body_list.index(node)
    nxt = body_list[idx + 1]
    test_text = ctx.text(node.test)
    body_text = ctx.text(node.body[0])
    else_text = ctx.text(nxt)
    return ["if " + test_text + ":\n    " + body_text + "\nelse:\n    " + else_text]


def _match_dup_augassign(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add) and isinstance(node.target, ast.Name)):
        return False
    body_list, _ = _get_body_list(node, ctx)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx == 0:
        return False
    prev = body_list[idx - 1]
    return _is_reassign_if(prev, ctx)


def _fix_dup_augassign(node, ctx):
    return [""]


def _match_missing_second_reverse(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = enclosing_function(node, ctx)
    if not func or not func.body or func.body[-1] is not node:
        return False
    name = node.value.id
    first = func.body[0]
    if not (isinstance(first, ast.Expr) and isinstance(first.value, ast.Call)
            and isinstance(first.value.func, ast.Attribute) and first.value.func.attr == "reverse"
            and isinstance(first.value.func.value, ast.Name) and first.value.func.value.id == name):
        return False
    count = 0
    for n in ast.walk(func):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "reverse"
                and isinstance(n.func.value, ast.Name) and n.func.value.id == name):
            count += 1
    return count == 1


def _fix_missing_second_reverse(node, ctx):
    name = node.value.id
    return [name + ".reverse()\n" + ctx.text(node)]


def _match_assign_from_reverse(node, ctx):
    return (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "reverse")


def _fix_assign_from_reverse(node, ctx):
    target = ctx.text(node.targets[0])
    src = ctx.text(node.value.func.value)
    return [target + " = " + src + ".copy()\n" + target + ".reverse()"]


def _match_return_reverse_call(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"
            and isinstance(node.value.func.value, ast.Name))


def _fix_return_reverse_call(node, ctx):
    name = node.value.func.value.id
    return [name + ".reverse()\nreturn " + name]


def _match_return_reverse_attr(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute)
            and node.value.attr == "reverse" and isinstance(node.value.value, ast.Name))


def _fix_return_reverse_attr(node, ctx):
    name = node.value.value.id
    return [name + ".reverse()\nreturn " + name]


def _match_subscript_call(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr in ("count", "append", "extend", "index"))


def _fix_subscript_call(node, ctx):
    idx = _get_subscript_index(node)
    return [ctx.text(node.value) + "(" + ctx.text(idx) + ")"]


def _match_builtin_bracket(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
            and node.value.id in ("len", "list", "int", "str"))


def _fix_builtin_bracket(node, ctx):
    idx = _get_subscript_index(node)
    return [ctx.text(node.value) + "(" + ctx.text(idx) + ")"]


def _match_eq_assign(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Compare)
            and len(node.value.ops) == 1 and isinstance(node.value.ops[0], ast.Eq)
            and isinstance(node.value.left, ast.Name))


def _fix_eq_assign(node, ctx):
    left = ctx.text(node.value.left)
    right = ctx.text(node.value.comparators[0])
    return [left + " = " + right]


def _match_ordereddict_import(node, ctx):
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef):
        return False
    if not func.body or func.body[0] is not node:
        return False
    uses = any(isinstance(n, ast.Name) and n.id == "OrderedDict" for n in ast.walk(func))
    if not uses:
        return False
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.ImportFrom) and n.module == "collections":
            if any(a.name == "OrderedDict" for a in n.names):
                return False
        if isinstance(n, ast.Import):
            if any(a.name == "collections" for a in n.names):
                return False
    return True


def _fix_ordereddict_import(node, ctx):
    return ["from collections import OrderedDict\n" + ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="iter_over_builtin_list", match=_match_iter_over_list,
                    replace=_fix_iter_over_list, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="membership_wrong_container", match=_match_membership_wrong,
                    replace=_fix_membership_wrong, symptoms=("wrong",)),
            Rewrite(name="append_call_on_undefined_name", match=_match_append_undefined,
                    replace=_fix_append_undefined, symptoms=("err:NameError", "wrong")),
            Rewrite(name="return_wrong_accumulator", match=_match_return_wrong,
                    replace=_fix_return_wrong, symptoms=("wrong",)),
            Rewrite(name="missing_call_parens", match=_match_missing_parens,
                    replace=_fix_missing_parens, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="missing_return_statement", match=_match_missing_return,
                    replace=_fix_missing_return, symptoms=("wrong",)),
            Rewrite(name="in_should_be_notin", match=_match_in_should_be_notin,
                    replace=_fix_in_should_be_notin, symptoms=("wrong",)),
            Rewrite(name="ordereddict_lists_typo", match=_match_lists_typo,
                    replace=_fix_lists_typo, symptoms=("err:NameError",)),
            Rewrite(name="ordereddict_missing_list_wrap", match=_match_return_fromkeys_bare,
                    replace=_fix_return_fromkeys_bare, symptoms=("wrong",)),
            Rewrite(name="augassign_needs_wrap", match=_match_augassign_wrap,
                    replace=_fix_augassign_wrap, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="reassign_if_missing_else", match=_is_reassign_if,
                    replace=_fix_reassign_if, symptoms=("wrong", "timeout")),
            Rewrite(name="dup_augassign_after_reassign", match=_match_dup_augassign,
                    replace=_fix_dup_augassign, symptoms=("wrong", "timeout")),
            Rewrite(name="missing_second_reverse", match=_match_missing_second_reverse,
                    replace=_fix_missing_second_reverse, symptoms=("wrong",)),
            Rewrite(name="assign_from_reverse", match=_match_assign_from_reverse,
                    replace=_fix_assign_from_reverse, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="return_reverse_call", match=_match_return_reverse_call,
                    replace=_fix_return_reverse_call, symptoms=("wrong",)),
            Rewrite(name="return_reverse_attr", match=_match_return_reverse_attr,
                    replace=_fix_return_reverse_attr, symptoms=("wrong",)),
            Rewrite(name="subscript_should_be_call", match=_match_subscript_call,
                    replace=_fix_subscript_call, symptoms=("err:TypeError",)),
            Rewrite(name="builtin_bracket_call", match=_match_builtin_bracket,
                    replace=_fix_builtin_bracket, symptoms=("err:TypeError",)),
            Rewrite(name="eq_should_be_assign", match=_match_eq_assign,
                    replace=_fix_eq_assign, symptoms=("wrong", "err:NameError")),
            Rewrite(name="missing_ordereddict_import", match=_match_ordereddict_import,
                    replace=_fix_ordereddict_import, symptoms=("err:NameError",)),
        ]