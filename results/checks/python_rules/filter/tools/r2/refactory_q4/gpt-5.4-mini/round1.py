from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_sort_age_function(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_compare_age(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.left, ast.Subscript)
        and ctx.text(node.left.slice) == "1"
    )


def _swap_lt_gt(node, ctx):
    op = node.ops[0]
    if isinstance(op, ast.Lt):
        return [f"{ctx.text(node.left)} > {ctx.text(node.comparators[0])}"]
    if isinstance(op, ast.Gt):
        return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]
    if isinstance(op, ast.LtE):
        return [f"{ctx.text(node.left)} >= {ctx.text(node.comparators[0])}"]
    if isinstance(op, ast.GtE):
        return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]
    return []


def _is_list_remove_wrong_var(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "remove"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_remove_to_selected(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Expr):
        return []
    if isinstance(node.func.value, ast.Name):
        return [f"{ctx.text(node.func.value)}.remove(smallest)"]
    return []


def _is_append_wrong_var(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_append_to_selected(node, ctx):
    if isinstance(node.func.value, ast.Name):
        return [f"{ctx.text(node.func.value)}.append(smallest)"]
    return []


def _is_return_reverse(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute) and node.value.attr == "reverse"


def _fix_return_reverse(node, ctx):
    return [ctx.text(node.value.value)]


def _is_return_none_print(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "print"


def _delete_print(node, ctx):
    return [""]


def _is_assign_sort_var(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in {"sort", "sorted", "result", "output", "new_list", "newlst", "lst1", "final", "a"}
    )


def _fix_assign_selected(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite("compare_age_direction", _is_compare_age, _swap_lt_gt, ("wrong",)),
            Rewrite("remove_selected_not_loop_var", _is_list_remove_wrong_var, _fix_remove_to_selected, ("wrong",)),
            Rewrite("append_selected_not_loop_var", _is_append_wrong_var, _fix_append_to_selected, ("wrong",)),
            Rewrite("return_value_instead_of_reverse_method", _is_return_reverse, _fix_return_reverse, ("wrong",)),
            Rewrite("delete_debug_print", _is_return_none_print, _delete_print, ("wrong",)),
        ]