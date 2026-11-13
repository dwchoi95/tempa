from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_sort_age(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_return_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name)


def _fix_return_name(node, ctx):
    if isinstance(node.value, ast.Name):
        return [f"return {ctx.text(node.value)}()"]
    return []


def _is_missing_return(node, ctx):
    return isinstance(node, ast.Pass)


def _delete_pass(node, ctx):
    return [""]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _is_strict_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _flip_lt_to_gt(node, ctx):
    return [f"{ctx.text(node.left)} > {ctx.text(node.comparators[0])}"]


def _flip_gt_to_lt(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]


def _is_wrong_remove_name(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "remove"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_remove_to_var(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.Expr):
        return [f"{ctx.text(node.func.value)}.remove(smallest)"]
    return []


def _is_remove_i_append_i(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _fix_append_to_smallest(node, ctx):
    txt = ctx.text(node)
    txt = txt.replace("append(i)", "append(smallest)")
    txt = txt.replace("append(oldest)", "append(oldest)")
    txt = txt.replace("append(biggest)", "append(biggest)")
    return [txt]


def _is_reverse_call_expr(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_reverse_call(node, ctx):
    return [f"{ctx.text(node.value.func.value)}.reverse()"]


def _is_return_reverse(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute) and node.value.attr == "reverse"


def _fix_return_reverse(node, ctx):
    return [f"{ctx.text(node.value.value)}.reverse()"]


def _is_list_reverse_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_list_reverse_return(node, ctx):
    return [ctx.text(node.value.func.value)]


def _is_pop_noarg(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "pop" and len(node.args) == 0


def _fix_pop_zero(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop(0)"]


def _is_wrong_swap(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 2
        and all(isinstance(t, ast.Subscript) for t in node.targets)
    )


def _fix_wrong_swap(node, ctx):
    if len(node.targets) == 2:
        return [f"{ctx.text(node.targets[0])}, {ctx.text(node.targets[1])} = {ctx.text(node.value.elts[0])}, {ctx.text(node.value.elts[1])}"] if isinstance(node.value, ast.Tuple) and len(node.value.elts) == 2 else []
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="remove_pass", match=_is_missing_return, replace=_delete_pass, symptoms=("wrong",)),
            Rewrite(name="return_name_should_be_returned", match=_is_return_name, replace=_fix_return_name, symptoms=("wrong",)),
            Rewrite(name="lt_to_gt", match=_is_strict_lt, replace=_flip_lt_to_gt, symptoms=("wrong",)),
            Rewrite(name="gt_to_lt", match=_is_strict_gt, replace=_flip_gt_to_lt, symptoms=("wrong",)),
            Rewrite(name="remove_should_target_selected_var", match=_is_wrong_remove_name, replace=_fix_remove_to_var, symptoms=("wrong",)),
            Rewrite(name="append_selected_var", match=_is_remove_i_append_i, replace=_fix_append_to_smallest, symptoms=("wrong",)),
            Rewrite(name="reverse_call_missing_parens", match=_is_reverse_call_expr, replace=_fix_reverse_call, symptoms=("wrong",)),
            Rewrite(name="return_reverse_method", match=_is_return_reverse, replace=_fix_return_reverse, symptoms=("wrong",)),
            Rewrite(name="return_reverse_call", match=_is_list_reverse_return, replace=_fix_list_reverse_return, symptoms=("wrong",)),
            Rewrite(name="pop_needs_zero_index", match=_is_pop_noarg, replace=_fix_pop_zero, symptoms=("wrong",)),
        ]