from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_sort_age(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_len_eq_one(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _to_len_lte_one(node, ctx):
    return [ctx.text(node.left) + " <= 1"]


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _return_expr_name(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.FunctionDef):
        return []
    return [ctx.text(node)]


def _is_wrong_return_reverse_call(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse" and len(node.value.args) == 0


def _remove_reverse_return(node, ctx):
    return [ctx.text(node.value.func.value)]


def _is_reverse_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "reverse"


def _call_reverse(node, ctx):
    return [ctx.text(node) + "()"]


def _is_list_reverse_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_reverse_return(node, ctx):
    return [ctx.text(node.value.func.value) + "[::-1]"]


def _is_remove_wrong_name(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "remove"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and isinstance(node.func.value, ast.Name)
        and node.args[0].id != node.func.value.id
    )


def _fix_remove_target(node, ctx):
    return [ctx.text(node.func.value) + ".remove(" + ctx.text(node.func.value) + ")"]


def _is_append_name_instead_of_tuple(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in ("append", "remove")
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_append_name(node, ctx):
    return [ctx.text(node.func.value) + "." + node.func.attr + "(" + ctx.text(node.args[0]) + ")"]


def _is_compare_age_lt(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Lt)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.right, ast.Subscript)
    )


def _flip_lt_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_compare_age_gt(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.right, ast.Subscript)
    )


def _flip_gt_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _is_sort_call_no_key(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "sort" and not node.keywords


def _add_age_key(node, ctx):
    return [ctx.text(node.func.value) + ".sort(key=lambda x: x[1], reverse=True)"]


def _is_append_pop_reverse(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute) and node.value.attr == "reverse"


def _call_reverse_return(node, ctx):
    return [ctx.text(node.value.value)]


def _is_pop_noarg(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "pop" and len(node.args) == 0


def _fix_pop_arg(node, ctx):
    return [ctx.text(node.func.value) + ".pop(0)"]


def _is_if_return_sort(node, ctx):
    return isinstance(node, ast.If) and any(isinstance(s, ast.Return) for s in node.body)


def _remove_early_return(node, ctx):
    src = ctx.text(node)
    return [src.replace("\n        return sort", "", 1).replace("\n        return new_list", "", 1).replace("\n        return result", "", 1)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="len_eq_one_should_allow_empty", match=_is_len_eq_one, replace=_to_len_lte_one, symptoms=("wrong",)),
            Rewrite(name="return_missing_value", match=_is_return_none, replace=_return_expr_name, symptoms=("wrong",)),
            Rewrite(name="reverse_method_needs_call", match=_is_reverse_attr, replace=_call_reverse, symptoms=("wrong",)),
            Rewrite(name="return_reverse_method_result", match=_is_wrong_return_reverse_call, replace=_remove_reverse_return, symptoms=("wrong",)),
            Rewrite(name="return_reverse_attribute_list", match=_is_list_reverse_return, replace=_fix_reverse_return, symptoms=("wrong",)),
            Rewrite(name="remove_wrong_variable", match=_is_remove_wrong_name, replace=_fix_remove_target, symptoms=("wrong",)),
            Rewrite(name="append_name_should_use_same_name", match=_is_append_name_instead_of_tuple, replace=_fix_append_name, symptoms=("wrong",)),
            Rewrite(name="age_compare_lt_should_gt", match=_is_compare_age_lt, replace=_flip_lt_to_gt, symptoms=("wrong",)),
            Rewrite(name="age_compare_gt_should_lt", match=_is_compare_age_gt, replace=_flip_gt_to_lt, symptoms=("wrong",)),
            Rewrite(name="sort_call_needs_key", match=_is_sort_call_no_key, replace=_add_age_key, symptoms=("wrong",)),
            Rewrite(name="pop_needs_zero_index", match=_is_pop_noarg, replace=_fix_pop_arg, symptoms=("wrong",)),
            Rewrite(name="early_return_in_loop", match=_is_if_return_sort, replace=_remove_early_return, symptoms=("wrong",)),
        ]