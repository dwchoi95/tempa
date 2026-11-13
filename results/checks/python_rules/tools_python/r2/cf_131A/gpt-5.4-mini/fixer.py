from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_call_attr(node, ctx, attr):
    return isinstance(node, ast.Attribute) and node.attr == attr and isinstance(ctx.parent(node), ast.Call) and ctx.parent(node).func is node


def _is_isupper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper" and isinstance(ctx.parent(node), ast.Call) and ctx.parent(node).func is node


def _match_title_to_swapcase(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "title" and len(node.args) == 0 and len(node.keywords) == 0


def _replace_title_to_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _match_capitalize_to_swapcase(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "capitalize" and len(node.args) == 0 and len(node.keywords) == 0


def _replace_capitalize_to_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _match_isupper_slice_misuse(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
        and len(node.args) == 0
        and len(node.keywords) == 0
        and isinstance(node.func.value, ast.Subscript)
    )


def _replace_isupper_slice_misuse(node, ctx):
    return [ctx.text(node.func.value) + ".upper() == " + ctx.text(node.func.value)]


def _match_isupper_attr_missing_call(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _replace_isupper_attr_missing_call(node, ctx):
    return [ctx.text(node) + "()"]


def _match_islower_attr_missing_call(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _replace_islower_attr_missing_call(node, ctx):
    return [ctx.text(node) + "()"]


def _match_islower_slice_misuse(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "islower"
        and len(node.args) == 0
        and len(node.keywords) == 0
        and isinstance(node.func.value, ast.Subscript)
    )


def _replace_islower_slice_misuse(node, ctx):
    return [ctx.text(node.func.value) + ".lower() == " + ctx.text(node.func.value)]


def _match_isupper_compare_to_lower(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Attribute)
        and node.left.func.attr == "isupper"
    )


def _replace_isupper_compare_to_lower(node, ctx):
    return [ctx.text(node.left.func.value) + ".upper() == " + ctx.text(node.left.func.value)]


def _match_lower_compare_to_self(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Attribute)
        and node.left.func.attr == "lower"
    )


def _replace_lower_compare_to_self(node, ctx):
    return [ctx.text(node.left.func.value) + ".lower() == " + ctx.text(node.left.func.value)]


def _match_len_eq_one_swapcase(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_len_eq_one_swapcase(node, ctx):
    return [ctx.text(node.left.args[0]) + ".swapcase()"]


def _match_len_gt_one_to_ge_one(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_len_gt_one_to_ge_one(node, ctx):
    return [ctx.text(node.left.args[0]) + ".__len__() >= 1"]


def _match_index_zero_to_slice(node, ctx):
    return isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Constant) and node.slice.value == 0


def _replace_index_zero_to_slice(node, ctx):
    return [ctx.text(node.value) + "[0:1]"]


def _match_or_to_and(node, ctx):
    return isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or)


def _replace_or_to_and(node, ctx):
    return [(" and ").join(ctx.text(v) for v in node.values)]


def _match_and_to_or(node, ctx):
    return isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And)


def _replace_and_to_or(node, ctx):
    return [(" or ").join(ctx.text(v) for v in node.values)]


def _match_swapcase_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "swapcase" and len(node.args) == 0 and len(node.keywords) == 0


def _replace_swapcase_call(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="title_to_swapcase", match=_match_title_to_swapcase, replace=_replace_title_to_swapcase, symptoms=("wrong",)),
            Rewrite(name="capitalize_to_swapcase", match=_match_capitalize_to_swapcase, replace=_replace_capitalize_to_swapcase, symptoms=("wrong",)),
            Rewrite(name="isupper_slice_misuse_to_compare", match=_match_isupper_slice_misuse, replace=_replace_isupper_slice_misuse, symptoms=("wrong",)),
            Rewrite(name="isupper_missing_call", match=_match_isupper_attr_missing_call, replace=_replace_isupper_attr_missing_call, symptoms=("wrong",)),
            Rewrite(name="islower_missing_call", match=_match_islower_attr_missing_call, replace=_replace_islower_attr_missing_call, symptoms=("wrong",)),
            Rewrite(name="islower_slice_misuse_to_compare", match=_match_islower_slice_misuse, replace=_replace_islower_slice_misuse, symptoms=("wrong",)),
            Rewrite(name="compare_isupper_to_upper_self", match=_match_isupper_compare_to_lower, replace=_replace_isupper_compare_to_lower, symptoms=("wrong",)),
            Rewrite(name="compare_lower_to_self", match=_match_lower_compare_to_self, replace=_replace_lower_compare_to_self, symptoms=("wrong",)),
            Rewrite(name="len_eq_one_to_swapcase", match=_match_len_eq_one_swapcase, replace=_replace_len_eq_one_swapcase, symptoms=("wrong",)),
            Rewrite(name="len_gt_one_to_ge_one", match=_match_len_gt_one_to_ge_one, replace=_replace_len_gt_one_to_ge_one, symptoms=("wrong",)),
            Rewrite(name="index_zero_to_slice", match=_match_index_zero_to_slice, replace=_replace_index_zero_to_slice, symptoms=("wrong",)),
            Rewrite(name="or_to_and", match=_match_or_to_and, replace=_replace_or_to_and, symptoms=("wrong",)),
            Rewrite(name="and_to_or", match=_match_and_to_or, replace=_replace_and_to_or, symptoms=("wrong",)),
            Rewrite(name="swapcase_call_identity", match=_match_swapcase_call, replace=_replace_swapcase_call, symptoms=("wrong",)),
        ]