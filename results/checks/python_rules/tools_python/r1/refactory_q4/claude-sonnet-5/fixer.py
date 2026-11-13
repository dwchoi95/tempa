from src.core.repair import Rule
import ast
import builtins
from src.core.rewrite import Rewrite

BUILTIN_NAMES = set(dir(builtins))


# ---------------------------------------------------------------- helpers --

def _ancestor_of_type(node, ctx, types):
    cur = ctx.parent(node)
    while cur is not None:
        if isinstance(cur, types):
            return cur
        cur = ctx.parent(cur)
    return None


def _enclosing_function(node, ctx):
    return _ancestor_of_type(node, ctx, ast.FunctionDef)


def _collect_local_names(func):
    names = set()
    for a in func.args.args:
        names.add(a.arg)
    for a in getattr(func.args, "kwonlyargs", []):
        names.add(a.arg)
    if func.args.vararg:
        names.add(func.args.vararg.arg)
    if func.args.kwarg:
        names.add(func.args.kwarg.arg)
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            names.add(n.id)
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
        if isinstance(n, ast.comprehension) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
    return names


def _slice_text_node(sl):
    if hasattr(ast, "Index") and isinstance(sl, ast.Index):
        return sl.value
    return sl


# ------------------------------------------------------- 1. missing return --

def _find_accumulator(func):
    for st in func.body:
        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name):
            if isinstance(st.value, (ast.List, ast.Tuple)) and len(st.value.elts) == 0:
                return st.targets[0].id
    return None


def _is_last_stmt_no_return(node, ctx):
    if isinstance(node, (ast.FunctionDef, ast.Module)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if ctx.field(node) != "body":
        return False
    if not parent.body or parent.body[-1] is not node:
        return False
    for n in ast.walk(parent):
        if isinstance(n, ast.Return):
            return False
    return _find_accumulator(parent) is not None


def _insert_return(node, ctx):
    parent = ctx.parent(node)
    acc = _find_accumulator(parent)
    if acc is None:
        return []
    if isinstance(node, ast.Pass):
        return ["return " + acc]
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and \
       isinstance(node.value.func, ast.Name) and node.value.func.id == "print":
        return ["return " + acc]
    return [ctx.text(node) + "\nreturn " + acc]


# ------------------------------------------------------- 2. undefined name --

def _is_undefined_name(node, ctx):
    if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    local = _collect_local_names(func)
    if node.id in local:
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        if node.id in BUILTIN_NAMES:
            return False
        mod_funcs = {f.name for f in ast.walk(ctx.tree) if isinstance(f, ast.FunctionDef)}
        if node.id in mod_funcs:
            return False
    return True


def _undefined_candidates(node, ctx):
    func = _enclosing_function(node, ctx)
    if func is None:
        return []
    local = _collect_local_names(func)
    return sorted(n for n in local if n != node.id)


# ----------------------------------------------- 3. swapped extremum assign --

def _is_swapped_assign(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    if not isinstance(node.value, ast.Name):
        return False
    parent_if = ctx.parent(node)
    if not isinstance(parent_if, ast.If) or ctx.field(node) != "body":
        return False
    for_node = _ancestor_of_type(parent_if, ctx, ast.For)
    if for_node is None or not isinstance(for_node.target, ast.Name):
        return False
    loop_var = for_node.target.id
    if node.targets[0].id != loop_var:
        return False
    if node.value.id == loop_var:
        return False
    return True


def _swap_assign(node, ctx):
    return [ctx.text(node.value) + " = " + ctx.text(node.targets[0])]


# --------------------------------------------------- 4. compare direction --

def _is_simple_compare(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1 and
            isinstance(node.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE)))


def _compare_candidates(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    cur = {ast.Lt: "<", ast.Gt: ">", ast.LtE: "<=", ast.GtE: ">="}[type(node.ops[0])]
    return [left + " " + o + " " + right for o in ("<", ">", "<=", ">=") if o != cur]


# ----------------------------------------------------- 5. empty tuple test --

def _is_empty_tuple_compare(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)
            and isinstance(node.comparators[0], ast.Tuple) and len(node.comparators[0].elts) == 0)


def _fix_empty_tuple(node, ctx):
    return [ctx.text(node.left) + " == []"]


# --------------------------------------------------- 6. subscript-as-call --

def _is_bad_subscript_call(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    if not isinstance(node.value, ast.Attribute):
        return False
    return node.value.attr in ("pop", "remove")


def _fix_subscript_call(node, ctx):
    sl = _slice_text_node(node.slice)
    return [ctx.text(node.value) + "(" + ctx.text(sl) + ")"]


# ------------------------------------------------- 7. self-append reassign --

def _is_self_append_assign(node, ctx):
    if not isinstance(node, ast.Assign) or len(node.targets) != 1:
        return False
    if not isinstance(node.targets[0], ast.Name):
        return False
    v = node.value
    if not (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "append"):
        return False
    if not isinstance(v.func.value, ast.Name):
        return False
    return v.func.value.id == node.targets[0].id


def _fix_self_append(node, ctx):
    return [ctx.text(node.value)]


# ----------------------------------------------------- 8. reverse(x) call --

def _is_reverse_with_args(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "reverse" and len(node.args) > 0)


def _fix_reverse_args(node, ctx):
    return [ctx.text(node.func) + "()"]


# ----------------------------------------- 9. bare-name tuple comparison --

def _is_bare_name_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and
            isinstance(node.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE))):
        return False
    return isinstance(node.left, ast.Name) and isinstance(node.comparators[0], ast.Name)


def _fix_bare_compare(node, ctx):
    op = {ast.Lt: "<", ast.Gt: ">", ast.LtE: "<=", ast.GtE: ">="}[type(node.ops[0])]
    return [ctx.text(node.left) + "[1] " + op + " " + ctx.text(node.comparators[0]) + "[1]"]


# --------------------------------------------------- 10. range off-by-one --

def _is_range_plus_one(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"):
        return False
    args = node.args
    if len(args) == 1:
        target = args[0]
    elif len(args) == 2:
        target = args[1]
    else:
        return False
    return (isinstance(target, ast.BinOp) and isinstance(target.op, ast.Add)
            and isinstance(target.right, ast.Constant) and target.right.value == 1
            and isinstance(target.left, ast.Call) and isinstance(target.left.func, ast.Name)
            and target.left.func.id == "len")


def _fix_range(node, ctx):
    args = node.args
    if len(args) == 1:
        return ["range(" + ctx.text(args[0].left) + ")"]
    return ["range(" + ctx.text(args[0]) + ", " + ctx.text(args[1].left) + ")"]


# --------------------------------------------- 11. return stuck inside loop --

def _is_while_trailing_return(node, ctx):
    if not isinstance(node, ast.While) or not node.body:
        return False
    return isinstance(node.body[-1], ast.Return)


def _dedent_return(node, ctx):
    last = node.body[-1]
    header = "while " + ctx.text(node.test) + ":"
    lines = [header]
    for s in node.body[:-1]:
        for ln in ctx.text(s).split("\n"):
            lines.append("    " + ln)
    lines.append(ctx.text(last))
    return ["\n".join(lines)]


# ----------------------------------------------- 12. missing accumulator --

def _find_uninitialized_accumulator(block, func):
    stores = set()
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            stores.add(n.id)
    for n in ast.walk(block):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == "append" and isinstance(n.func.value, ast.Name)):
            if n.func.value.id not in stores:
                return n.func.value.id
    return None


def _is_block_needing_init(node, ctx):
    if not isinstance(node, (ast.While, ast.For)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef) or ctx.field(node) != "body":
        return False
    return _find_uninitialized_accumulator(node, parent) is not None


def _insert_init(node, ctx):
    parent = ctx.parent(node)
    name = _find_uninitialized_accumulator(node, parent)
    if name is None:
        return []
    return [name + " = []\n" + ctx.text(node)]


# ------------------------------------------------- 13/14. bad return forms --

def _is_return_attr_no_call(node, ctx):
    return (isinstance(node, ast.Return) and node.value is not None
            and isinstance(node.value, ast.Attribute) and node.value.attr in ("reverse", "sort"))


def _fix_return_attr(node, ctx):
    obj = ctx.text(node.value.value)
    return [obj + ".reverse()\nreturn " + obj, "return " + obj]


def _is_return_reverse_call(node, ctx):
    return (isinstance(node, ast.Return) and node.value is not None and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute) and node.value.func.attr in ("reverse", "sort"))


def _fix_return_reverse_call(node, ctx):
    obj = ctx.text(node.value.func.value)
    call_text = ctx.text(node.value)
    return [call_text + "\nreturn " + obj]


# -------------------------------------------- 15. reverse() stuck in loop --

def _get_reverse_obj(stmt):
    if isinstance(stmt, ast.Expr):
        v = stmt.value
        if isinstance(v, ast.Attribute) and v.attr == "reverse":
            return v.value
        if isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "reverse":
            return v.func.value
    return None


def _is_while_trailing_reverse(node, ctx):
    if not isinstance(node, ast.While) or not node.body:
        return False
    return _get_reverse_obj(node.body[-1]) is not None


def _hoist_reverse(node, ctx):
    obj = _get_reverse_obj(node.body[-1])
    obj_text = ctx.text(obj)
    header = "while " + ctx.text(node.test) + ":"
    lines = [header]
    for s in node.body[:-1]:
        for ln in ctx.text(s).split("\n"):
            lines.append("    " + ln)
    lines.append(obj_text + ".reverse()")
    return ["\n".join(lines)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="missing_return_insert", match=_is_last_stmt_no_return,
                    replace=_insert_return, symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="undefined_name_candidates", match=_is_undefined_name,
                    replace=_undefined_candidates, symptoms=("err:NameError", "wrong")),
            Rewrite(name="swapped_extremum_assign", match=_is_swapped_assign,
                    replace=_swap_assign, symptoms=("wrong",)),
            Rewrite(name="compare_direction_candidates", match=_is_simple_compare,
                    replace=_compare_candidates, symptoms=("wrong",)),
            Rewrite(name="empty_tuple_should_be_list", match=_is_empty_tuple_compare,
                    replace=_fix_empty_tuple, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="subscript_should_be_call", match=_is_bad_subscript_call,
                    replace=_fix_subscript_call, symptoms=("err:TypeError",)),
            Rewrite(name="unwrap_self_append_assign", match=_is_self_append_assign,
                    replace=_fix_self_append, symptoms=("wrong",)),
            Rewrite(name="reverse_takes_no_args", match=_is_reverse_with_args,
                    replace=_fix_reverse_args, symptoms=("err:TypeError",)),
            Rewrite(name="bare_name_compare_needs_index", match=_is_bare_name_compare,
                    replace=_fix_bare_compare, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="range_off_by_one", match=_is_range_plus_one,
                    replace=_fix_range, symptoms=("err:IndexError", "wrong")),
            Rewrite(name="dedent_trailing_return_from_while", match=_is_while_trailing_return,
                    replace=_dedent_return, symptoms=("wrong",)),
            Rewrite(name="init_missing_accumulator", match=_is_block_needing_init,
                    replace=_insert_init, symptoms=("err:NameError",)),
            Rewrite(name="return_attribute_without_call", match=_is_return_attr_no_call,
                    replace=_fix_return_attr, symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="return_reverse_call_result", match=_is_return_reverse_call,
                    replace=_fix_return_reverse_call, symptoms=("wrong",)),
            Rewrite(name="hoist_reverse_out_of_while", match=_is_while_trailing_reverse,
                    replace=_hoist_reverse, symptoms=("wrong",)),
        ]