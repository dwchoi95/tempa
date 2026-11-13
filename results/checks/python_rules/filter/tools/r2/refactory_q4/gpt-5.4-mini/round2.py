from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_constant(node, ctx, value=None):
    return isinstance(node, ast.Constant) and (value is None or node.value == value)


def _is_remove_selected_append_selected(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    if not isinstance(node.value, ast.Call):
        return False
    call = node.value
    if not isinstance(call.func, ast.Attribute):
        return False
    if call.func.attr not in {"remove", "append"} or len(call.args) != 1:
        return False
    arg = call.args[0]
    if not isinstance(arg, ast.Name):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return False
    stmts = parent.body
    try:
        idx = stmts.index(node)
    except ValueError:
        return False
    if idx == 0:
        return False
    prev = stmts[idx - 1]
    if not isinstance(prev, ast.Assign) or len(prev.targets) != 1:
        return False
    target = prev.targets[0]
    return isinstance(target, ast.Name) and target.id == arg.id


def _fix_remove_selected_append_selected(node, ctx):
    call = node.value
    prev = ctx.parent(node).body[ctx.parent(node).body.index(node) - 1]
    var = prev.targets[0].id
    func = call.func.attr
    return [f"{ctx.text(call.func.value)}.{func}({var})"]


def _is_remove_selected_and_append_selected_stmt(node, ctx):
    if not isinstance(node, ast.Expr) or not isinstance(node.value, ast.Call):
        return False
    call = node.value
    if not isinstance(call.func, ast.Attribute) or len(call.args) != 1:
        return False
    if call.func.attr not in {"remove", "append"}:
        return False
    return isinstance(call.args[0], ast.Name)


def _fix_return_sort(node, ctx):
    if isinstance(node, ast.Return):
        return ["return " + ctx.text(node.value)] if node.value else []
    return []


def _is_wrong_empty_tuple_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.comparators[0], ast.Tuple)
        and len(node.comparators[0].elts) == 0
    )


def _fix_empty_tuple_check(node, ctx):
    return [ctx.text(node.left) + " == []"]


def _is_sort_call_reverse(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) is False and ctx.text(node).strip() == "return sort.reverse()"


def _fix_reverse_return(node, ctx):
    return ["return sort"]


def _is_reverse_method_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute) and node.value.attr == "reverse"


def _fix_reverse_method_return(node, ctx):
    return [f"return {ctx.text(node.value.value)}"]


def _is_append_call_on_name(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and len(node.value.args) == 1


def _fix_append_name(node, ctx):
    call = node.value
    arg = call.args[0]
    if isinstance(arg, ast.Name):
        return [f"{ctx.text(call.func.value)}.append({ctx.text(arg)})"]
    return []


def _is_remove_name_vs_selected(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "remove" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Name)


def _fix_remove_name_vs_selected(node, ctx):
    prev = ctx.parent(node).body[ctx.parent(node).body.index(node) - 1]
    if isinstance(prev, ast.Assign) and len(prev.targets) == 1 and isinstance(prev.targets[0], ast.Name):
        return [f"{ctx.text(node.value.func.value)}.remove({prev.targets[0].id})"]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite("remove_selected_not_loop_var", _is_remove_selected_append_selected, _fix_remove_selected_append_selected, ("wrong",)),
            Rewrite("append_selected_not_loop_var", _is_remove_selected_append_selected, _fix_remove_selected_append_selected, ("wrong",)),
            Rewrite("return_variable_not_builtin_sort", lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Name) and n.value.id == "sort", _fix_return_sort, ("wrong",)),
            Rewrite("empty_tuple_check_should_be_empty_list", _is_wrong_empty_tuple_check, _fix_empty_tuple_check, ("wrong",)),
            Rewrite("reverse_method_return_should_return_list", _is_reverse_method_return, _fix_reverse_method_return, ("wrong",)),
            Rewrite("append_selected_name", _is_append_call_on_name, _fix_append_name, ("wrong",)),
            Rewrite("remove_selected_name", _is_remove_name_vs_selected, _fix_remove_name_vs_selected, ("wrong",)),
        ]