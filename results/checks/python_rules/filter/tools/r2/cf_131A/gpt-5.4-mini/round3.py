from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_isupper_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_islower_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "islower"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_isupper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _is_islower_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _is_upper_on_slice(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "upper"
        and isinstance(node.func.value, ast.Subscript)
    )


def _replace_upper_slice_truthy(node, ctx):
    sub = node.func.value
    if not isinstance(sub.slice, ast.Slice):
        return []
    return [f"{ctx.text(sub.value)}[{ctx.text(sub.slice.lower) if sub.slice.lower else ''}:{ctx.text(sub.slice.upper) if sub.slice.upper else ''}] == {ctx.text(sub.value)}[{ctx.text(sub.slice.lower) if sub.slice.lower else ''}:{ctx.text(sub.slice.upper) if sub.slice.upper else ''}].upper()"]


def _replace_isupper_attr(node, ctx):
    return [ctx.text(node) + "()"]


def _replace_islower_attr(node, ctx):
    return [ctx.text(node) + "()"]


def _replace_capitalize_to_swapcase(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "capitalize":
        return [ctx.text(node.func.value) + ".swapcase()"]
    return []


def _replace_title_to_swapcase(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "title":
        return [ctx.text(node.func.value) + ".swapcase()"]
    return []


def _replace_upper_to_lower(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "upper":
        return [ctx.text(node.func.value) + ".lower()"]
    return []


def _replace_lower_to_upper(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "lower":
        return [ctx.text(node.func.value) + ".upper()"]
    return []


def _fix_or_slice_condition(node, ctx):
    if not isinstance(node, ast.BoolOp) or not isinstance(node.op, ast.Or) or len(node.values) != 2:
        return False
    left, right = node.values
    return _is_isupper_call(left, ctx) and isinstance(right, ast.Call) and isinstance(right.func, ast.Attribute) and right.func.attr == "isupper" and isinstance(right.func.value, ast.Subscript)


def _replace_or_with_and(node, ctx):
    left, right = node.values
    return [f"{ctx.text(left)} and {ctx.text(right)}"]


def _fix_len_one_and_isupper(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.And)
        and len(node.values) == 2
        and isinstance(node.values[0], ast.Compare)
        and isinstance(node.values[1], ast.Call)
        and isinstance(node.values[1].func, ast.Attribute)
        and node.values[1].func.attr == "isupper"
    )


def _replace_len_one_and_isupper(node, ctx):
    return [f"len({ctx.text(node.values[0].left)}) == 1 or {ctx.text(node.values[1].func.value)}.isupper()"]


def _fix_wrong_single_letter_upper(node, ctx):
    return (
        isinstance(node, ast.If)
        and len(node.body) == 1
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Call)
        and isinstance(node.body[0].value.func, ast.Name)
        and node.body[0].value.func.id == "print"
    )


class Fixer:
    def rules(self):
        return [
            Rewrite(name="call_missing_parens_isupper", match=_is_isupper_attr, replace=_replace_isupper_attr, symptoms=("wrong",)),
            Rewrite(name="call_missing_parens_islower", match=_is_islower_attr, replace=_replace_islower_attr, symptoms=("wrong",)),
            Rewrite(name="slice_upper_truthy_to_equality", match=_is_upper_on_slice, replace=_replace_upper_slice_truthy, symptoms=("wrong",)),
            Rewrite(name="capitalize_to_swapcase", match=_replace_capitalize_to_swapcase, replace=_replace_capitalize_to_swapcase, symptoms=("wrong",)),
            Rewrite(name="title_to_swapcase", match=_replace_title_to_swapcase, replace=_replace_title_to_swapcase, symptoms=("wrong",)),
            Rewrite(name="upper_to_lower_call", match=_replace_upper_to_lower, replace=_replace_upper_to_lower, symptoms=("wrong",)),
            Rewrite(name="lower_to_upper_call", match=_replace_lower_to_upper, replace=_replace_lower_to_upper, symptoms=("wrong",)),
            Rewrite(name="or_slice_check_should_use_and", match=_fix_or_slice_condition, replace=_replace_or_with_and, symptoms=("wrong",)),
            Rewrite(name="len_one_and_isupper_to_or", match=_fix_len_one_and_isupper, replace=_replace_len_one_and_isupper, symptoms=("wrong",)),
        ]