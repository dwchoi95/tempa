from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
    )


def _is_isupper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _is_islower_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _is_istitle_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "istitle"


def _is_swapcase_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "swapcase"
    )


def _is_upper_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "upper"
    )


def _is_lower_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "lower"
    )


def _match_title_for_swapcase(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "title"
    )


def _replace_title_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _match_capitalize_for_swapcase(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "capitalize"
    )


def _replace_capitalize_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _match_missing_isupper_call(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _replace_missing_isupper_call(node, ctx):
    return [ctx.text(node) + "()"]


def _match_missing_islower_call(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _replace_missing_islower_call(node, ctx):
    return [ctx.text(node) + "()"]


def _match_upper_to_isupper(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "upper"


def _replace_upper_to_isupper(node, ctx):
    return [ctx.text(node.func.value) + ".isupper()"]


def _match_lower_to_islower(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "lower"


def _replace_lower_to_islower(node, ctx):
    return [ctx.text(node.func.value) + ".islower()"]


def _match_singleton_and_upper(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.And)
        and len(node.values) == 2
        and isinstance(node.values[0], ast.Compare)
        and isinstance(node.values[1], ast.Call)
        and isinstance(node.values[1].func, ast.Attribute)
        and node.values[1].func.attr == "isupper"
    )


def _replace_singleton_and_upper(node, ctx):
    return [ctx.text(node.values[0].left) + ".islower() and " + ctx.text(node.values[1])]


def _match_len_gt_one(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_len_gt_one(node, ctx):
    return [ctx.text(node.left.args[0]) + " == 1"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="title_should_be_swapcase",
                match=_match_title_for_swapcase,
                replace=_replace_title_with_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="capitalize_should_be_swapcase",
                match=_match_capitalize_for_swapcase,
                replace=_replace_capitalize_with_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_isupper_call",
                match=_match_missing_isupper_call,
                replace=_replace_missing_isupper_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_islower_call",
                match=_match_missing_islower_call,
                replace=_replace_missing_islower_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="upper_call_used_as_predicate",
                match=_match_upper_to_isupper,
                replace=_replace_upper_to_isupper,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lower_call_used_as_predicate",
                match=_match_lower_to_islower,
                replace=_replace_lower_to_islower,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="singleton_and_upper_should_be_lower_check",
                match=_match_singleton_and_upper,
                replace=_replace_singleton_and_upper,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_gt_one_should_be_len_eq_one",
                match=_match_len_gt_one,
                replace=_replace_len_gt_one,
                symptoms=("wrong",),
            ),
        ]