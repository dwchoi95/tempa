from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_call_attr(node, ctx, attr):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == attr and len(node.args) == 0 and len(node.keywords) == 0


def _is_attr(node, ctx, attr):
    return isinstance(node, ast.Attribute) and node.attr == attr


def _is_boolish_method_misuse(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr in {"upper", "lower", "islower", "isupper", "capitalize", "title"} and not isinstance(ctx.parent(node), ast.Call)


def _replace_attr_call(node, ctx):
    return [ctx.text(node) + "()"]


def _replace_swapcase(node, ctx):
    if isinstance(node, ast.Attribute) and node.attr in {"title", "capitalize"}:
        return [ctx.text(node.value) + ".swapcase()"]
    return []


def _match_len1_isupper(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.And)
        and len(node.values) == 2
        and isinstance(node.values[0], ast.Compare)
        and isinstance(node.values[1], ast.Call)
        and _is_call_attr(node.values[1], ctx, "isupper")
        and isinstance(node.values[0].ops[0], ast.Eq)
        and isinstance(node.values[0].left, ast.Call)
        and _is_name(node.values[0].left.func, ctx, "len")
        and len(node.values[0].left.args) == 1
        and isinstance(node.values[0].comparators[0], ast.Constant)
        and node.values[0].comparators[0].value == 1
    )


def _replace_len1_guard(node, ctx):
    return [f"len({ctx.text(node.values[0].left.args[0])}) == 1 or {ctx.text(node.values[1])}"]


def _match_or_trueish(node, ctx):
    return isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and any(
        isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr in {"upper", "lower", "capitalize", "title"}
        and len(v.args) == 0 and len(v.keywords) == 0 and not isinstance(ctx.parent(v), ast.Compare)
        for v in node.values
    )


def _replace_or_call_truth(node, ctx):
    text = ctx.text(node)
    for v in node.values:
        if isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr in {"upper", "lower", "capitalize", "title"}:
            return [text.replace(ctx.text(v), f"{ctx.text(v.func.value)}.{v.func.attr}()")]
    return []


def _match_missing_call(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr in {"isupper", "islower", "upper", "lower", "capitalize", "title"}


class Fixer:
    def rules(self):
        return [
            Rewrite(name="attribute_method_needs_call", match=_is_boolish_method_misuse, replace=_replace_attr_call, symptoms=("wrong",)),
            Rewrite(name="swapcase_for_title_or_capitalize_fix", match=_replace_swapcase, replace=_replace_swapcase, symptoms=("wrong",)),
            Rewrite(name="len1_should_be_or_guard", match=_match_len1_isupper, replace=_replace_len1_guard, symptoms=("wrong",)),
            Rewrite(name="or_with_method_truthiness_should_call_method", match=_match_or_trueish, replace=_replace_or_call_truth, symptoms=("wrong",)),
            Rewrite(name="missing_method_call_generic", match=_match_missing_call, replace=_replace_attr_call, symptoms=("wrong",)),
        ]