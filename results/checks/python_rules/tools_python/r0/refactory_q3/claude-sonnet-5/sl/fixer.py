from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ----------------------------------------------------------------------
# generic helpers
# ----------------------------------------------------------------------

def _get_body_list(parent, node):
    if parent is None:
        return None
    for _field, value in ast.iter_fields(parent):
        if isinstance(value, list) and node in value:
            return value
    return None


def _enclosing_func(node, ctx):
    cur = ctx.parent(node)
    while cur is not None and not isinstance(cur, ast.FunctionDef):
        cur = ctx.parent(cur)
    return cur


def _enclosing_if(node, ctx):
    cur = node
    while cur is not None and not isinstance(cur, ast.If):
        cur = ctx.parent(cur)
    return cur


def _edit_distance(a, b):
    if a == b:
        return 0
    dp = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        prev = dp[0]
        dp[0] = i
        for j, cb in enumerate(b, 1):
            cur = dp[j]
            dp[j] = prev if ca == cb else 1 + min(prev, dp[j], dp[j - 1])
            prev = cur
    return dp[-1]


def _close(a, b):
    if a == b:
        return False
    if min(len(a), len(b)) < 4:
        return False
    if abs(len(a) - len(b)) > 2:
        return False
    return _edit_distance(a, b) <= 2


def _accumulator_from_if(if_node):
    if if_node is None:
        return None
    for stmt in if_node.body:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            f = stmt.value.func
            if (isinstance(f, ast.Attribute) and f.attr in ('append', 'extend', 'insert')
                    and isinstance(f.value, ast.Name)):
                return f.value.id
        if (isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name)
                and isinstance(stmt.op, ast.Add)):
            return stmt.target.id
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)):
            v = stmt.value
            if (isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add)
                    and isinstance(v.left, ast.Name) and v.left.id == stmt.targets[0].id):
                return stmt.targets[0].id
    return None


def _find_accumulator_in_func(func):
    for stmt in func.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            val = stmt.value
            if isinstance(val, ast.List):
                return stmt.targets[0].id
    return None


def _name_initialized_as_list(name, func):
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                and n.targets[0].id == name and isinstance(n.value, ast.List)):
            return True
    return False


def _bound_names(func):
    names = set(a.arg for a in func.args.args)
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            names.add(n.id)
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
    return names


# ----------------------------------------------------------------------
# rule: variable shadowed by builtin `list`
# ----------------------------------------------------------------------

def _match_shadowed_list(node, ctx):
    if not (isinstance(node, ast.Name) and node.id == 'list' and isinstance(node.ctx, ast.Load)):
        return False
    func = _enclosing_func(node, ctx)
    if func is None or not func.args.args:
        return False
    if 'list' in (a.arg for a in func.args.args):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    return True


def _fix_shadowed_list(node, ctx):
    func = _enclosing_func(node, ctx)
    return [func.args.args[0].arg]


# ----------------------------------------------------------------------
# rule: `if x not in ORIGINAL:` should check the accumulator
# ----------------------------------------------------------------------

def _match_wrong_in_target(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.In, ast.NotIn))):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    comparator = node.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    acc = _accumulator_from_if(parent)
    if acc is None or acc == comparator.id:
        return False
    return True


def _fix_wrong_in_target(node, ctx):
    parent = ctx.parent(node)
    acc = _accumulator_from_if(parent)
    op_text = "not in" if isinstance(node.ops[0], ast.NotIn) else "in"
    return [f"{ctx.text(node.left)} {op_text} {acc}"]


# ----------------------------------------------------------------------
# rule: duplicate kept because polarity of membership test is flipped
# ----------------------------------------------------------------------

def _match_flip_in(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.In)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    comparator = node.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    acc = _accumulator_from_if(parent)
    return acc is not None and acc == comparator.id


def _fix_flip_in(node, ctx):
    return [f"{ctx.text(node.left)} not in {ctx.text(node.comparators[0])}"]


# ----------------------------------------------------------------------
# rule: `x != final` / `x == final` instead of membership test
# ----------------------------------------------------------------------

def _match_wrong_eq_membership(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], (ast.Eq, ast.NotEq))):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    comparator = node.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    acc = _accumulator_from_if(parent)
    return acc is not None and acc == comparator.id


def _fix_wrong_eq_membership(node, ctx):
    op_text = "not in" if isinstance(node.ops[0], ast.NotEq) else "in"
    return [f"{ctx.text(node.left)} {op_text} {ctx.text(node.comparators[0])}"]


# ----------------------------------------------------------------------
# rule: chained `in ... == True` style comparison
# ----------------------------------------------------------------------

def _match_chained_extra_compare(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 2
            and isinstance(node.ops[0], ast.In) and isinstance(node.ops[1], ast.Eq))


def _fix_chained_extra_compare(node, ctx):
    return [f"{ctx.text(node.left)} in {ctx.text(node.comparators[0])}"]


# ----------------------------------------------------------------------
# rule: append/extend/insert target mismatched to the tested accumulator
# ----------------------------------------------------------------------

def _match_wrong_append_target(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in ('append', 'extend', 'insert')):
        return False
    if not isinstance(node.func.value, ast.Name):
        return False
    stmt = ctx.parent(node)
    if not isinstance(stmt, ast.Expr):
        return False
    if_node = ctx.parent(stmt)
    if not isinstance(if_node, ast.If):
        return False
    if stmt not in if_node.body and stmt not in if_node.orelse:
        return False
    test = if_node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], (ast.In, ast.NotIn))):
        return False
    comparator = test.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    return node.func.value.id != comparator.id


def _fix_wrong_append_target(node, ctx):
    stmt = ctx.parent(node)
    if_node = ctx.parent(stmt)
    comparator = if_node.test.comparators[0]
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [f"{ctx.text(comparator)}.{node.func.attr}({args_text})"]


# ----------------------------------------------------------------------
# rule: `.count()` called on the wrong (original) list
# ----------------------------------------------------------------------

def _match_wrong_count_target(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'count'):
        return False
    if not isinstance(node.func.value, ast.Name):
        return False
    if_node = _enclosing_if(ctx.parent(node), ctx)
    if if_node is None:
        return False
    acc = _accumulator_from_if(if_node)
    return acc is not None and acc != node.func.value.id


def _fix_wrong_count_target(node, ctx):
    if_node = _enclosing_if(ctx.parent(node), ctx)
    acc = _accumulator_from_if(if_node)
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [f"{acc}.count({args_text})"]


# ----------------------------------------------------------------------
# rule: `X = X.append(y)` self reassignment of a void method
# ----------------------------------------------------------------------

def _match_self_assign_append(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    val = node.value
    if not (isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute)
            and val.func.attr in ('append', 'extend', 'insert')):
        return False
    if not isinstance(val.func.value, ast.Name):
        return False
    return val.func.value.id == node.targets[0].id


def _fix_self_assign_append(node, ctx):
    return [ctx.text(node.value)]


def _match_self_augassign_append(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)):
        return False
    val = node.value
    return (isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute)
            and val.func.attr in ('append', 'extend', 'insert'))


def _fix_self_augassign_append(node, ctx):
    return [ctx.text(node.value)]


# ----------------------------------------------------------------------
# rule: `X.append.item` (dotted instead of called)
# ----------------------------------------------------------------------

def _match_dotted_append_arg(node, ctx):
    return (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Attribute)
            and node.value.attr in ('append', 'extend', 'insert')
            and isinstance(ctx.parent(node), ast.Expr))


def _fix_dotted_append_arg(node, ctx):
    return [f"{ctx.text(node.value)}({node.attr})"]


# ----------------------------------------------------------------------
# rule: `X.append[y]` subscript instead of call
# ----------------------------------------------------------------------

def _match_subscript_as_call(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr in ('append', 'extend', 'insert', 'count'))


def _fix_subscript_as_call(node, ctx):
    sl = node.slice
    if isinstance(sl, ast.Index):
        sl = sl.value
    return [f"{ctx.text(node.value)}({ctx.text(sl)})"]


# ----------------------------------------------------------------------
# rule: `name == []` meant as `name = []`
# ----------------------------------------------------------------------

def _match_eq_as_assign_init(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Compare)
            and len(node.value.ops) == 1 and isinstance(node.value.ops[0], ast.Eq)
            and isinstance(node.value.left, ast.Name)
            and isinstance(node.value.comparators[0], ast.List)
            and len(node.value.comparators[0].elts) == 0)


def _fix_eq_as_assign_init(node, ctx):
    return [f"{ctx.text(node.value.left)} = []"]


# ----------------------------------------------------------------------
# rule: returning / assigning the result of a void mutating method
# ----------------------------------------------------------------------

_VOID_METHODS = {'reverse', 'sort'}


def _match_return_void_method(node, ctx):
    if not isinstance(node, ast.Return) or not isinstance(node.value, ast.Call):
        return False
    f = node.value.func
    if not (isinstance(f, ast.Attribute) and f.attr in _VOID_METHODS and isinstance(f.value, ast.Name)):
        return False
    return not node.value.args and not node.value.keywords


def _fix_return_void_method(node, ctx):
    obj = ctx.text(node.value.func.value)
    attr = node.value.func.attr
    return [f"{obj}.{attr}()\nreturn {obj}"]


def _match_assign_void_method(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    val = node.value
    if not (isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute)
            and val.func.attr in _VOID_METHODS and isinstance(val.func.value, ast.Name)):
        return False
    return not val.args and not val.keywords


def _fix_assign_void_method(node, ctx):
    obj = ctx.text(node.value.func.value)
    attr = node.value.func.attr
    target = ctx.text(node.targets[0])
    return [f"{obj}.{attr}()\n{target} = {obj}"]


def _match_bare_method_call(node, ctx):
    if not (isinstance(node, ast.Attribute) and node.attr in ('reverse', 'pop', 'sort')):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and ctx.field(node) == 'func':
        return False
    return isinstance(parent, (ast.Expr, ast.Return))


def _fix_bare_method_call(node, ctx):
    return [ctx.text(node) + "()"]


# ----------------------------------------------------------------------
# rule: missing `from collections import OrderedDict`
# ----------------------------------------------------------------------

def _has_ordereddict_import(tree):
    for n in ast.walk(tree):
        if isinstance(n, ast.ImportFrom) and n.module == 'collections':
            for alias in n.names:
                if alias.name == 'OrderedDict':
                    return True
        if isinstance(n, ast.Import):
            for alias in n.names:
                if alias.name == 'collections':
                    return True
    return False


def _match_missing_import(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    if not any(isinstance(n, ast.Name) and n.id == 'OrderedDict' for n in ast.walk(node.value)):
        return False
    return not _has_ordereddict_import(ctx.tree)


def _fix_missing_import(node, ctx):
    return ["from collections import OrderedDict", ctx.text(node)]


def _match_bare_fromkeys(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == 'fromkeys'):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name) and parent.func.id == 'list':
        return False
    return True


def _fix_bare_fromkeys(node, ctx):
    return [f"list({ctx.text(node)})"]


def _match_lists_typo(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'lists'


def _fix_lists_typo(node, ctx):
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [f"list({args_text})"]


# ----------------------------------------------------------------------
# rule: typo'd call to a sibling function
# ----------------------------------------------------------------------

def _match_typo_call_name(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)):
        return False
    name = node.func.id
    funcs = [f.name for f in ast.walk(ctx.tree) if isinstance(f, ast.FunctionDef)]
    if name in funcs:
        return False
    candidates = [f for f in funcs if _close(f, name)]
    return len(candidates) == 1


def _fix_typo_call_name(node, ctx):
    funcs = [f.name for f in ast.walk(ctx.tree) if isinstance(f, ast.FunctionDef)]
    name = node.func.id
    candidates = [f for f in funcs if _close(f, name)]
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [f"{candidates[0]}({args_text})"]


# ----------------------------------------------------------------------
# rule: generic typo'd variable name
# ----------------------------------------------------------------------

def _match_typo_name(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    func = _enclosing_func(node, ctx)
    if func is None:
        return False
    bound = _bound_names(func)
    if node.id in bound:
        return False
    candidates = [n for n in bound if _close(n, node.id)]
    return len(candidates) == 1


def _fix_typo_name(node, ctx):
    func = _enclosing_func(node, ctx)
    bound = _bound_names(func)
    candidates = [n for n in bound if _close(n, node.id)]
    return [candidates[0]]


# ----------------------------------------------------------------------
# rule: accumulator used without ever being initialised
# ----------------------------------------------------------------------

def _accumulator_candidate_for_for(for_node):
    for n in ast.walk(for_node):
        if (isinstance(n, ast.If) and isinstance(n.test, ast.Compare) and len(n.test.ops) == 1
                and isinstance(n.test.ops[0], ast.NotIn)):
            comp = n.test.comparators[0]
            if isinstance(comp, ast.Name) and _accumulator_from_if(n) == comp.id:
                return comp.id
    return None


def _match_missing_init(node, ctx):
    if not isinstance(node, ast.For):
        return False
    acc = _accumulator_candidate_for_for(node)
    if acc is None:
        return False
    func = _enclosing_func(node, ctx)
    if func is None or acc in (a.arg for a in func.args.args):
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == acc for t in n.targets):
            return False
    return True


def _fix_missing_init(node, ctx):
    acc = _accumulator_candidate_for_for(node)
    return [f"{acc} = []\n{ctx.text(node)}"]


# ----------------------------------------------------------------------
# rule: index/removal shift bug -- unconditional increment after mutation
# ----------------------------------------------------------------------

def _match_if_needs_else(node, ctx):
    if not isinstance(node, ast.If) or node.orelse:
        return False
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx + 1 >= len(body_list):
        return False
    nxt = body_list[idx + 1]
    return isinstance(nxt, ast.AugAssign) and isinstance(nxt.op, ast.Add)


def _fix_if_needs_else(node, ctx):
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    idx = body_list.index(node)
    nxt = body_list[idx + 1]
    body_lines = "\n    ".join(ctx.text(s) for s in node.body)
    return [f"if {ctx.text(node.test)}:\n    {body_lines}\nelse:\n    {ctx.text(nxt)}"]


def _match_redundant_augassign(node, ctx):
    if not isinstance(node, ast.AugAssign):
        return False
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx == 0:
        return False
    prev = body_list[idx - 1]
    if not isinstance(prev, ast.If) or len(prev.orelse) != 1:
        return False
    return ctx.text(prev.orelse[0]) == ctx.text(node)


def _fix_redundant_augassign(node, ctx):
    return [""]


# ----------------------------------------------------------------------
# rule: boolean flag reset outside the loop instead of inside it
# ----------------------------------------------------------------------

def _match_flag_before_for(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    if not (isinstance(node.value, ast.Constant) and isinstance(node.value.value, bool)):
        return False
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx + 1 >= len(body_list):
        return False
    nxt = body_list[idx + 1]
    if not isinstance(nxt, ast.For):
        return False
    name = node.targets[0].id
    return any(isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
               and n.targets[0].id == name for n in ast.walk(nxt))


def _fix_flag_before_for(node, ctx):
    return [""]


def _match_for_needs_flag(node, ctx):
    if not isinstance(node, ast.For):
        return False
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    if body_list is None:
        return False
    idx = body_list.index(node)
    if idx == 0:
        return False
    prev = body_list[idx - 1]
    if not (isinstance(prev, ast.Assign) and len(prev.targets) == 1 and isinstance(prev.targets[0], ast.Name)
            and isinstance(prev.value, ast.Constant) and isinstance(prev.value.value, bool)):
        return False
    name = prev.targets[0].id
    return any(isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
               and n.targets[0].id == name for n in ast.walk(node))


def _fix_for_needs_flag(node, ctx):
    parent = ctx.parent(node)
    body_list = _get_body_list(parent, node)
    idx = body_list.index(node)
    prev = body_list[idx - 1]
    header = f"for {ctx.text(node.target)} in {ctx.text(node.iter)}:"
    body_lines = "\n    ".join(ctx.text(s) for s in node.body)
    return [f"{header}\n    {ctx.text(prev)}\n    {body_lines}"]


# ----------------------------------------------------------------------
# rule: return of a mismatched accumulator name
# ----------------------------------------------------------------------

def _match_return_mismatch(node, ctx):
    if not isinstance(node, ast.Return) or not isinstance(node.value, ast.Name):
        return False
    func = _enclosing_func(node, ctx)
    if func is None:
        return False
    acc = _find_accumulator_in_func(func)
    return acc is not None and acc != node.value.id


def _fix_return_mismatch(node, ctx):
    func = _enclosing_func(node, ctx)
    acc = _find_accumulator_in_func(func)
    return [f"return {acc}"]


# ----------------------------------------------------------------------
# rule: `acc += scalar` / `acc = acc + scalar` should wrap in a list
# ----------------------------------------------------------------------

def _match_augassign_scalar(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add) and isinstance(node.target, ast.Name)):
        return False
    if isinstance(node.value, (ast.List, ast.Tuple)):
        return False
    func = _enclosing_func(node, ctx)
    if func is None:
        return False
    return _name_initialized_as_list(node.target.id, func)


def _fix_augassign_scalar(node, ctx):
    return [f"{ctx.text(node.target)} += [{ctx.text(node.value)}]"]


def _match_binop_scalar(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Assign) and len(parent.targets) == 1
            and isinstance(parent.targets[0], ast.Name)):
        return False
    if not (isinstance(node.left, ast.Name) and node.left.id == parent.targets[0].id):
        return False
    if isinstance(node.right, (ast.List, ast.Tuple)):
        return False
    func = _enclosing_func(node, ctx)
    if func is None:
        return False
    return _name_initialized_as_list(parent.targets[0].id, func)


def _fix_binop_scalar(node, ctx):
    return [f"{ctx.text(node.left)} + [{ctx.text(node.right)}]"]


# ----------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="shadowed_list_param", match=_match_shadowed_list,
                    replace=_fix_shadowed_list, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="wrong_in_target", match=_match_wrong_in_target,
                    replace=_fix_wrong_in_target, symptoms=("wrong",)),
            Rewrite(name="flip_in_for_dedup", match=_match_flip_in,
                    replace=_fix_flip_in, symptoms=("wrong",)),
            Rewrite(name="wrong_eq_membership", match=_match_wrong_eq_membership,
                    replace=_fix_wrong_eq_membership, symptoms=("wrong",)),
            Rewrite(name="chained_extra_compare", match=_match_chained_extra_compare,
                    replace=_fix_chained_extra_compare, symptoms=("wrong",)),
            Rewrite(name="wrong_append_target", match=_match_wrong_append_target,
                    replace=_fix_wrong_append_target, symptoms=("err:NameError", "wrong")),
            Rewrite(name="wrong_count_target", match=_match_wrong_count_target,
                    replace=_fix_wrong_count_target, symptoms=("wrong",)),
            Rewrite(name="self_assign_append", match=_match_self_assign_append,
                    replace=_fix_self_assign_append, symptoms=("wrong",)),
            Rewrite(name="self_augassign_append", match=_match_self_augassign_append,
                    replace=_fix_self_augassign_append, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="dotted_append_arg", match=_match_dotted_append_arg,
                    replace=_fix_dotted_append_arg, symptoms=("err:AttributeError", "wrong")),
            Rewrite(name="subscript_as_call", match=_match_subscript_as_call,
                    replace=_fix_subscript_as_call, symptoms=("err:TypeError",)),
            Rewrite(name="eq_as_assign_init", match=_match_eq_as_assign_init,
                    replace=_fix_eq_as_assign_init, symptoms=("err:NameError",)),
            Rewrite(name="return_void_method", match=_match_return_void_method,
                    replace=_fix_return_void_method, symptoms=("wrong",)),
            Rewrite(name="assign_void_method", match=_match_assign_void_method,
                    replace=_fix_assign_void_method, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="bare_method_call_missing_parens", match=_match_bare_method_call,
                    replace=_fix_bare_method_call, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="missing_ordereddict_import", match=_match_missing_import,
                    replace=_fix_missing_import, symptoms=("err:NameError",)),
            Rewrite(name="bare_fromkeys_wrap", match=_match_bare_fromkeys,
                    replace=_fix_bare_fromkeys, symptoms=("wrong",)),
            Rewrite(name="lists_typo", match=_match_lists_typo,
                    replace=_fix_lists_typo, symptoms=("err:NameError",)),
            Rewrite(name="typo_call_name", match=_match_typo_call_name,
                    replace=_fix_typo_call_name, symptoms=("err:NameError",)),
            Rewrite(name="typo_name_generic", match=_match_typo_name,
                    replace=_fix_typo_name, symptoms=("err:NameError", "wrong")),
            Rewrite(name="missing_accumulator_init", match=_match_missing_init,
                    replace=_fix_missing_init, symptoms=("err:NameError",)),
            Rewrite(name="if_needs_else_before_augassign", match=_match_if_needs_else,
                    replace=_fix_if_needs_else, symptoms=("wrong", "timeout")),
            Rewrite(name="redundant_augassign_after_if", match=_match_redundant_augassign,
                    replace=_fix_redundant_augassign, symptoms=("wrong",)),
            Rewrite(name="flag_before_for_delete", match=_match_flag_before_for,
                    replace=_fix_flag_before_for, symptoms=("wrong",)),
            Rewrite(name="flag_reset_inside_for", match=_match_for_needs_flag,
                    replace=_fix_for_needs_flag, symptoms=("wrong",)),
            Rewrite(name="return_mismatched_accumulator", match=_match_return_mismatch,
                    replace=_fix_return_mismatch, symptoms=("err:NameError", "wrong")),
            Rewrite(name="augassign_wrap_scalar", match=_match_augassign_scalar,
                    replace=_fix_augassign_scalar, symptoms=("err:TypeError",)),
            Rewrite(name="binop_wrap_scalar", match=_match_binop_scalar,
                    replace=_fix_binop_scalar, symptoms=("err:TypeError",)),
        ]