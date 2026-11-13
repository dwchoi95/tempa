from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_isupper_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "isupper" and not isinstance(getattr(node, "ctx", None), ast.Store)


def _is_islower_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "islower" and not isinstance(getattr(node, "ctx", None), ast.Store)


def _is_isupper_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "isupper" and len(node.args) == 0 and len(node.keywords) == 0


def _is_islower_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "islower" and len(node.args) == 0 and len(node.keywords) == 0


def _is_isupper_call_or_attr(node, ctx):
    return _is_isupper_call(node, ctx) or _is_isupper_attr(node, ctx)


def _is_islower_call_or_attr(node, ctx):
    return _is_islower_call(node, ctx) or _is_islower_attr(node, ctx)


def _is_upper_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "upper" and len(node.args) == 0 and len(node.keywords) == 0


def _is_lower_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "lower" and len(node.args) == 0 and len(node.keywords) == 0


def _replace_title_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _replace_capitalize_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _replace_upper_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _replace_lower_with_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _match_title_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "title" and len(node.args) == 0 and len(node.keywords) == 0


def _match_capitalize_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "capitalize" and len(node.args) == 0 and len(node.keywords) == 0


def _match_upper_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "upper" and len(node.args) == 0 and len(node.keywords) == 0


def _match_lower_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "lower" and len(node.args) == 0 and len(node.keywords) == 0


def _match_isupper_attr(node, ctx):
    return _is_isupper_attr(node, ctx)


def _match_islower_attr(node, ctx):
    return _is_islower_attr(node, ctx)


def _fix_isupper_attr(node, ctx):
    return [ctx.text(node) + "()"]


def _fix_islower_attr(node, ctx):
    return [ctx.text(node) + "()"]


def _match_subslice_upper(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq) and (
        (isinstance(node.left, ast.Subscript) and _is_upper_call(node.comparators[0], ctx)) or
        (isinstance(node.comparators[0], ast.Subscript) and _is_upper_call(node.left, ctx))
    )


def _fix_subslice_upper(node, ctx):
    if isinstance(node.left, ast.Subscript):
        return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _match_len_eq_one(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq) and (
        (isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == "len" and len(node.left.args) == 1 and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 1) or
        (isinstance(node.comparators[0], ast.Call) and isinstance(node.comparators[0].func, ast.Name) and node.comparators[0].func.id == "len" and len(node.comparators[0].args) == 1 and isinstance(node.left, ast.Constant) and node.left.value == 1)
    )


def _fix_len_eq_one(node, ctx):
    if isinstance(node.left, ast.Call):
        return [ctx.text(node.left.args[0]) + "[1:] == " + ctx.text(node.left.args[0]) + "[1:].upper()"]
    return [ctx.text(node.comparators[0].args[0]) + "[1:] == " + ctx.text(node.comparators[0].args[0]) + "[1:].upper()"]


def _match_bool_attr_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in {"isupper", "islower"} and len(node.args) == 0 and len(node.keywords) == 0


def _fix_missing_parens_isupper(node, ctx):
    return [ctx.text(node.func.value) + "." + node.func.attr + "()"]


def _match_wrong_capitalize(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in {"capitalize", "title"} and len(node.args) == 0 and len(node.keywords) == 0


def _fix_wrong_capitalize(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="title_to_swapcase", match=_match_title_call, replace=_replace_title_with_swapcase, symptoms=("wrong",)),
            Rewrite(name="capitalize_to_swapcase", match=_match_capitalize_call, replace=_replace_capitalize_with_swapcase, symptoms=("wrong",)),
            Rewrite(name="upper_to_swapcase", match=_match_upper_call, replace=_replace_upper_with_swapcase, symptoms=("wrong",)),
            Rewrite(name="lower_to_swapcase", match=_match_lower_call, replace=_replace_lower_with_swapcase, symptoms=("wrong",)),
            Rewrite(name="missing_isupper_call", match=_match_isupper_attr, replace=_fix_isupper_attr, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="missing_islower_call", match=_match_islower_attr, replace=_fix_islower_attr, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="subscript_upper_compare", match=_match_subslice_upper, replace=_fix_subslice_upper, symptoms=("wrong",)),
            Rewrite(name="len_eq_one_should_use_suffix_check", match=_match_len_eq_one, replace=_fix_len_eq_one, symptoms=("wrong",)),
            Rewrite(name="capitalize_or_title_to_swapcase", match=_match_wrong_capitalize, replace=_fix_wrong_capitalize, symptoms=("wrong",)),
        ]