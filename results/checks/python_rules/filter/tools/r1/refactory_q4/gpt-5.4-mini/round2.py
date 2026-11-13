from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_sort_age_func(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_return_name_sort(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "sort"


def _replace_return_sort_with_correct_name(node, ctx):
    return [f"return {ctx.text(node.value)}t"]


def _is_return_noneish(node, ctx):
    return isinstance(node, ast.Return) and (
        node.value is None
        or (isinstance(node.value, ast.Name) and node.value.id in {"sort", "new_lst", "new_list", "output", "result", "sort1", "final"})
        or (isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse")
    )


def _replace_return_reverse(node, ctx):
    txt = ctx.text(node.value)
    if txt.endswith(".reverse"):
        txt += "()"
    return [f"return {txt}"]


def _is_remove_wrong_target(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
        and len(node.value.args) == 1
    )


def _replace_remove_with_lhs(node, ctx):
    call = node.value
    arg = call.args[0]
    if isinstance(arg, ast.Name):
        return [f"{ctx.text(call.func.value)}.remove({ctx.text(arg)})"]
    return []


def _is_append_wrong_target(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
    )


def _replace_append_with_selected(node, ctx):
    call = node.value
    arg = call.args[0]
    return [f"{ctx.text(call.func.value)}.append({ctx.text(arg)})"]


def _is_assign_selected_none(node, ctx):
    return isinstance(node, ast.Assign) and isinstance(node.value, ast.Name) and node.value.id in {"n", "i", "k", "x", "element", "person"}


def _replace_assign_selected_with_self(node, ctx):
    return [ctx.text(node).replace(" = n", " = " + ctx.text(node.value)).replace(" = x", " = " + ctx.text(node.value)).replace(" = i", " = " + ctx.text(node.value))]


def _is_compare_lt_to_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and (
        isinstance(node.ops[0], ast.Lt) or isinstance(node.ops[0], ast.LtE)
    )


def _replace_compare_flip(node, ctx):
    return [f"{ctx.text(node.left)} > {ctx.text(node.comparators[0])}"]


def _is_compare_gt_to_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _replace_compare_flip_gt(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]


def _is_sort_reverse_call_missing_parens(node, ctx):
    return isinstance(node, ast.Expr) and ctx.text(node).endswith(".reverse")


def _replace_add_parens(node, ctx):
    return [ctx.text(node) + "()"]


def _is_list_remove_index(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "remove" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Name)


def _replace_remove_index(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite("return_sort_to_sortt", _is_return_name_sort, _replace_return_sort_with_correct_name, ("wrong",)),
            Rewrite("return_reverse_call", _is_sort_reverse_func if False else _is_sort_reverse_call_missing_parens, _replace_add_parens, ("wrong",)),
            Rewrite("remove_selected_variable", _is_remove_wrong_target, lambda n, c: [f"{c.text(n.value.func.value)}.remove({c.text(n.value.args[0])})"], ("wrong",)),
            Rewrite("append_selected_variable", _is_append_wrong_target, _replace_append_with_selected, ("wrong",)),
            Rewrite("flip_lt_to_gt", _is_compare_lt_to_gt, _replace_compare_flip, ("wrong",)),
            Rewrite("flip_gt_to_lt", _is_compare_gt_to_lt, _replace_compare_flip_gt, ("wrong",)),
        ]