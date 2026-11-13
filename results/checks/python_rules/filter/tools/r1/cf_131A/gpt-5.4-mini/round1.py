from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_isupper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _is_islower_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _is_istitle_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "istitle"


def _is_upper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "upper"


def _is_lower_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "lower"


def _is_swapcase_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "swapcase"


def _match_len_eq_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_len_eq_1(node, ctx):
    arg = ctx.text(node.left.args[0])
    return [f"len({arg}) == 1 or {arg}.isupper()"]


def _match_bad_input_slice_isupper(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
        and isinstance(node.func.value, ast.Subscript)
    )


def _replace_bad_input_slice_isupper(node, ctx):
    base = ctx.text(node.func.value.value)
    return [f"{base}[1:].upper() == {base}[1:]"]


def _match_title_or_capitalize(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in {"title", "capitalize"}


def _replace_with_swapcase(node, ctx):
    base = ctx.text(node.func.value)
    return [f"{base}.swapcase()"]


def _match_isupper_return_lower(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Call)
        and isinstance(node.test.func, ast.Attribute)
        and node.test.func.attr == "isupper"
        and len(node.body) == 1
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Call)
        and isinstance(node.body[0].value.func, ast.Attribute)
        and node.body[0].value.func.attr in {"capitalize", "title"}
    )


def _replace_isupper_return_lower(node, ctx):
    s = ctx.text(node.test.func.value)
    return [f"if {s}.isupper():\n    print({s}.lower())"]


def _match_isupper_then_capitalize(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Call)
        and isinstance(node.test.func, ast.Attribute)
        and node.test.func.attr == "isupper"
        and any(isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Attribute) and stmt.value.func.attr == "capitalize" for stmt in node.body)
    )


def _replace_isupper_then_swapcase(node, ctx):
    s = ctx.text(node.test.func.value)
    return [f"if {s}.isupper():\n    print({s}.swapcase())"]


def _match_wrong_slice_cond(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Slice)
        and node.left.slice.lower is not None
        and isinstance(node.left.slice.lower, ast.Constant)
        and node.left.slice.lower.value == 1
        and isinstance(node.left.ctx, ast.Load)
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Attribute)
        and node.comparators[0].func.attr == "upper"
    )


def _replace_wrong_slice_cond(node, ctx):
    base = ctx.text(node.left.value)
    return [f"{base}[1:].upper() == {base}[1:]"]


def _match_isupper_call_on_slice(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
        and isinstance(node.func.value, ast.Subscript)
        and isinstance(node.func.value.slice, ast.Slice)
    )


def _replace_isupper_call_on_slice(node, ctx):
    base = ctx.text(node.func.value.value)
    sl = ctx.text(node.func.value)
    return [f"{sl}.upper() == {sl}"]


def _match_isupper_or_sliceisupper(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "isupper" for v in node.values)
        and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "isupper" and isinstance(v.func.value, ast.Subscript) for v in node.values)
    )


def _replace_isupper_or_sliceisupper(node, ctx):
    parts = [ctx.text(v) for v in node.values]
    return [" or ".join(parts)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="len_one_should_pass_capslock", match=_match_len_eq_1, replace=_replace_len_eq_1, symptoms=("wrong",)),
            Rewrite(name="slice_isupper_should_compare_upper", match=_match_bad_input_slice_isupper, replace=_replace_bad_input_slice_isupper, symptoms=("wrong",)),
            Rewrite(name="title_or_capitalize_to_swapcase", match=_match_title_or_capitalize, replace=_replace_with_swapcase, symptoms=("wrong",)),
            Rewrite(name="isupper_branch_should_lower", match=_match_isupper_return_lower, replace=_replace_isupper_return_lower, symptoms=("wrong",)),
            Rewrite(name="isupper_branch_should_swapcase", match=_match_isupper_then_capitalize, replace=_replace_isupper_then_swapcase, symptoms=("wrong",)),
            Rewrite(name="slice_upper_check_fixed", match=_match_wrong_slice_cond, replace=_replace_wrong_slice_cond, symptoms=("wrong",)),
            Rewrite(name="slice_isupper_call_fixed", match=_match_isupper_call_on_slice, replace=_replace_isupper_call_on_slice, symptoms=("wrong",)),
            Rewrite(name="or_of_isupper_checks_normalized", match=_match_isupper_or_sliceisupper, replace=_replace_isupper_or_sliceisupper, symptoms=("wrong",)),
        ]