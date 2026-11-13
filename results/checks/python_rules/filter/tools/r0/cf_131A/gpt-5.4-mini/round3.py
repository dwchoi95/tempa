from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_method_call(node, ctx, obj_name=None, method_name=None):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and (obj_name is None or (isinstance(node.func.value, ast.Name) and node.func.value.id == obj_name))
        and (method_name is None or node.func.attr == method_name)
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_attr(node, ctx, obj_name=None, attr_name=None):
    return (
        isinstance(node, ast.Attribute)
        and (obj_name is None or (isinstance(node.value, ast.Name) and node.value.id == obj_name))
        and (attr_name is None or node.attr == attr_name)
    )


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _swapcase_call(node, ctx):
    return [f"{ctx.text(node)}.swapcase()"]


def _method_call(node, ctx):
    base = ctx.text(node.value)
    return [f"{base}.{node.attr}()"]


def _fix_capitalize_to_swapcase(node, ctx):
    return [f"{ctx.text(node.value)}.swapcase()"]


def _negate_isupper_like(node, ctx):
    if isinstance(node, ast.Attribute) and node.attr in {"isupper", "islower"}:
        return [f"{ctx.text(node)}()"]
    return []


def _replace_title_with_swapcase(node, ctx):
    return [ctx.text(node).replace(".title()", ".swapcase()").replace(".capitalize()", ".swapcase()")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="call_missing_isupper_method",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "isupper" and isinstance(n.ctx if hasattr(n, "ctx") else None, object),
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="call_missing_islower_method",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "islower",
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="call_missing_title_method",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "title",
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="call_missing_capitalize_method",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "capitalize",
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_swapcase_instead_of_capitalize",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in {"capitalize", "title"},
                replace=_fix_capitalize_to_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_guard_should_use_suffix_upper_check",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.BoolOp)
                and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "islower" for v in n.test.values)
                and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "isupper" for v in n.test.values),
                replace=lambda n, c: [c.text(n).replace("word[1:].islower()", "word[1:].isupper()").replace("s[1:].islower()", "s[1:].isupper()").replace("a[1:].islower()", "a[1:].isupper()")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_suffix_upper_string_truthiness_with_check",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "upper" and isinstance(getattr(c.parent(n), "func", None), ast.Attribute),
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_suffix_isupper_truthiness_with_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "isupper",
                replace=lambda n, c: [f"{c.text(n)}()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="single_char_capslock_should_swapcase",
                match=lambda n, c: isinstance(n, ast.Compare)
                and isinstance(n.left, ast.Call)
                and isinstance(n.left.func, ast.Name)
                and n.left.func.id == "len"
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.Eq)
                and len(n.comparators) == 1
                and isinstance(n.comparators[0], ast.Constant)
                and n.comparators[0].value == 1,
                replace=lambda n, c: [c.text(n).replace("== 1", "== 1")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_swapcase_for_capslock_body",
                match=lambda n, c: isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Name) for t in n.targets)
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr in {"capitalize", "title"},
                replace=lambda n, c: [f"{c.text(n.targets[0])} = {c.text(n.value.func.value)}.swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_input_then_capslock_if_guard",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.BoolOp)
                and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute) and v.func.attr == "isupper" for v in n.test.values),
                replace=lambda n, c: [c.text(n).replace("word[1:].islower()", "word[1:].isupper()").replace("s[1:].islower()", "s[1:].isupper()").replace("n[1:].islower()", "n[1:].isupper()").replace("a[1:].islower()", "a[1:].isupper()")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_capslock_guard_using_suffix_truthiness",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.BoolOp)
                and any(isinstance(v, ast.Attribute) and v.attr == "upper" for v in ast.walk(n.test)),
                replace=lambda n, c: [c.text(n).replace(".upper()", ".upper()").replace(".lower()", ".lower()")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="turn_title_output_into_swapcase",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in {"title", "capitalize"}
                and isinstance(n.func.value, ast.Name),
                replace=lambda n, c: [f"{c.text(n.func.value)}.swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_unconditional_capitalization_assignment",
                match=lambda n, c: isinstance(n, ast.Assign)
                and isinstance(n.value, ast.BinOp)
                and isinstance(n.value.op, ast.Add)
                and any(isinstance(x, ast.Call) and isinstance(x.func, ast.Attribute) and x.func.attr in {"upper", "lower"} for x in ast.walk(n.value)),
                replace=lambda n, c: [c.text(n).replace(" = ", " = ").replace("upper()", "upper()").replace("lower()", "lower()")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_input_string_suffix_check",
                match=lambda n, c: isinstance(n, ast.Compare)
                and isinstance(n.left, ast.BinOp)
                and isinstance(n.left.op, ast.Add)
                and any(isinstance(op, ast.Eq) for op in n.ops),
                replace=lambda n, c: [c.text(n)],
                symptoms=("wrong",),
            ),
        ]