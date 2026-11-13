from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
    )


def _is_isupper_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
    )


def _is_islower_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "islower"
    )


def _is_string_slice(node, ctx):
    return isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice)


def _slice_text(node, ctx, start=None, stop=None):
    if not isinstance(node, ast.Subscript) or not isinstance(node.slice, ast.Slice):
        return None
    sl = node.slice
    if start is not None and (sl.lower is None or ctx.text(sl.lower) != start):
        return None
    if stop is not None and (sl.upper is None or ctx.text(sl.upper) != stop):
        return None
    if sl.step is not None:
        return None
    return ctx.text(node.value) + "[" + (
        "" if sl.lower is None else ctx.text(sl.lower)
    ) + ":" + (
        "" if sl.upper is None else ctx.text(sl.upper)
    ) + "]"


def _replace_isupper_call(node, ctx):
    return [ctx.text(node.func.value) + ".isupper()"]


def _replace_slice_isupper(node, ctx):
    if _is_isupper_call(node, ctx) and isinstance(node.func, ast.Attribute):
        return [ctx.text(node.func.value) + ".isupper()"]
    return []


def _match_any(node, ctx):
    return True


def _replace_call_attr_missing_parens(node, ctx):
    if isinstance(node, ast.Attribute) and node.attr in {"isupper", "islower", "isalpha", "islower"}:
        return [ctx.text(node) + "()"]
    return []


def _match_capitalize_for_capslock(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in {
        "capitalize",
        "title",
    }


def _replace_swapcase(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in {
        "capitalize",
        "title",
    }:
        return [ctx.text(node.func.value) + ".swapcase()"]
    return []


def _match_wrong_swapcase_guard(node, ctx):
    if not isinstance(node, ast.If):
        return False
    src = ctx.text(node.test)
    return ("isupper" in src or "islower" in src or "capitalize" in src or "title" in src) and "swapcase" in "".join(
        ctx.text(s) for s in node.body
    )


def _replace_if_with_len1_or_rest_upper(node, ctx):
    if not isinstance(node, ast.If):
        return []
    text = ctx.text(node.test)
    if "isupper" in text and "len(" not in text and "word[1:]" in text or "s[1:]" in text or "n[1:]" in text:
        return [ctx.text(node).replace(ctx.text(node.test), f"len({ctx.text(node.test).split('or')[0].strip().split('(')[-1].split('.')[0]}) == 1 or {ctx.text(node.test)}")]
    return []


def _match_len1_isupper(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp)
        and any(isinstance(v, ast.Compare) for v in ast.walk(node.test))
    )


def _replace_len1_isupper(node, ctx):
    return [ctx.text(node).replace("and", "or").replace("isupper()", "islower()")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="use_swapcase_instead_of_capitalize_or_title",
                match=_match_capitalize_for_capslock,
                replace=_replace_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="call_missing_isupper_parens",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr in {"isupper", "islower", "isalpha"},
                replace=_replace_call_attr_missing_parens,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="slice_isupper_should_be_method_call",
                match=lambda n, c: _is_isupper_call(n, c)
                and isinstance(n.func, ast.Attribute)
                and isinstance(n.func.value, ast.Subscript),
                replace=_replace_slice_isupper,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="input_then_capslock_swapcase_guard",
                match=lambda n, c: isinstance(n, ast.If)
                and "swapcase" in ctx.text(n)
                and "capitalize" in ctx.text(n.test) or "title" in ctx.text(n.test),
                replace=_replace_if_with_len1_or_rest_upper,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_capitalize_logic_on_capslock",
                match=lambda n, c: isinstance(n, ast.If)
                and "isupper" in ctx.text(n.test)
                and "capitalize" in ctx.text(n.body[0]) if isinstance(n, ast.If) and n.body else False,
                replace=_replace_len1_isupper,
                symptoms=("wrong",),
            ),
        ]