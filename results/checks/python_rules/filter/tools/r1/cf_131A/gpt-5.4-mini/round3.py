from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_call(node, ctx, name=None):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and (
        name is None or node.func.attr == name
    )


def _is_method_truthiness(node, ctx, method):
    return isinstance(node, ast.Attribute) and node.attr == method


def _call_text(node, ctx):
    return f"{ctx.text(node)}()"


def _replace_method_truthiness(node, ctx):
    return [f"{ctx.text(node)}()"]


def _match_upper_or_isupper(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and (
            (_is_method_truthiness(node.values[0], ctx, "isupper") and not isinstance(node.values[0], ast.Call))
            or (_is_method_truthiness(node.values[1], ctx, "isupper") and not isinstance(node.values[1], ast.Call))
            or (_is_method_truthiness(node.values[0], ctx, "islower") and not isinstance(node.values[0], ast.Call))
            or (_is_method_truthiness(node.values[1], ctx, "islower") and not isinstance(node.values[1], ast.Call))
        )
    )


def _replace_truthy_method_call(node, ctx):
    left, right = node.values
    if isinstance(left, ast.Attribute) and left.attr in {"isupper", "islower"} and not isinstance(left, ast.Call):
        return [f"{ctx.text(left)}() or {ctx.text(right)}"]
    if isinstance(right, ast.Attribute) and right.attr in {"isupper", "islower"} and not isinstance(right, ast.Call):
        return [f"{ctx.text(left)} or {ctx.text(right)}()"]
    return []


def _match_if_test_upper_or_slice_upper(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Eq)
        and (
            (isinstance(node.test.left, ast.Subscript) and isinstance(node.test.comparators[0], ast.Call))
            or (isinstance(node.test.left, ast.Call) and isinstance(node.test.comparators[0], ast.Subscript))
        )
    )


def _replace_eq_to_swapcase_title(node, ctx):
    return [ctx.text(node).replace("title()", "swapcase()").replace("capitalize()", "swapcase()")]


def _match_title_on_caps_condition(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in {"title", "capitalize"}
    )


def _replace_title_with_swapcase(node, ctx):
    return [f"{ctx.text(node.func.value)}.swapcase()"]


def _match_bad_upper_method_truthiness(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr in {"isupper", "islower"}


def _replace_missing_method_call(node, ctx):
    return [f"{ctx.text(node)}()"]


def _match_swapcase_if_all_upper_or_suffix_upper(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp)
        and isinstance(node.test.op, ast.Or)
        and any(
            isinstance(v, ast.Call)
            and isinstance(v.func, ast.Attribute)
            and v.func.attr in {"isupper", "islower"}
            for v in node.test.values
        )
    )


def _replace_if_to_swapcase(node, ctx):
    text = ctx.text(node)
    text = text.replace(".title()", ".swapcase()").replace(".capitalize()", ".swapcase()")
    return [text]


def _match_len1_and_isupper(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp)
        and isinstance(node.test.op, ast.And)
        and len(node.test.values) == 2
        and any(
            isinstance(v, ast.Compare)
            and len(v.ops) == 1
            and isinstance(v.ops[0], ast.Eq)
            and isinstance(v.left, ast.Call)
            for v in node.test.values
        )
    )


def _replace_len1_and_upper(node, ctx):
    return [ctx.text(node).replace("and", "or", 1).replace("isupper()", "islower()")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="call_method_when_used_as_boolean",
                match=_match_upper_or_isupper,
                replace=_replace_truthy_method_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_method_call_on_isupper_or_islower",
                match=_match_bad_upper_method_truthiness,
                replace=_replace_missing_method_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_title_capitalize_with_swapcase",
                match=_match_title_on_caps_condition,
                replace=_replace_title_with_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="if_condition_eq_uppercase_string_should_swapcase",
                match=_match_if_test_upper_or_slice_upper,
                replace=_replace_eq_to_swapcase_title,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_for_capslock_branching",
                match=_match_swapcase_if_all_upper_or_suffix_upper,
                replace=_replace_if_to_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len1_and_upper_should_be_len1_or_upper",
                match=_match_len1_and_isupper,
                replace=_replace_len1_and_upper,
                symptoms=("wrong",),
            ),
        ]