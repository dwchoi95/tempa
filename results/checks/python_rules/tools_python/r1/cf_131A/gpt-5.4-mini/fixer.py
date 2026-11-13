from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_input_assign(node):
    return isinstance(node, ast.Assign) and len(node.targets) == 1 and _is_input_call(node.value)


def _lhs_name(node):
    return isinstance(node, ast.Name) and node.id


def _is_isupper_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "isupper"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_isupper_attr(node):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _is_swapcase_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "swapcase"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_islower_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "islower"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_upper_slice_compare(node):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Attribute)
        and node.comparators[0].func.attr == "upper"
    )


def _slice_text(ctx, sub):
    return ctx.text(sub)


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_assignment_variable_normalization",
                match=lambda n, ctx: _is_input_assign(n)
                and isinstance(n.targets[0], ast.Name)
                and n.targets[0].id != "s",
                replace=lambda n, ctx: [f"s = {ctx.text(n.value)}"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="capitalize_to_swapcase_in_simple_print",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name)
                and n.func.id == "print"
                and len(n.args) == 1
                and isinstance(n.args[0], ast.Call)
                and isinstance(n.args[0].func, ast.Attribute)
                and n.args[0].func.attr in ("capitalize", "title", "lower"),
                replace=lambda n, ctx: [
                    "print(" + ctx.text(n.args[0].func.value) + ".swapcase())"
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="capitalize_to_swapcase_attribute",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in ("capitalize", "title")
                and len(n.args) == 0
                and len(n.keywords) == 0,
                replace=lambda n, ctx: [ctx.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="uppercase_check_should_be_slice_upper_or_len1",
                match=lambda n, ctx: isinstance(n, ast.If)
                and isinstance(n.test, ast.BoolOp)
                and any(
                    isinstance(v, ast.Compare)
                    and isinstance(v.left, ast.Subscript)
                    for v in n.test.values
                ),
                replace=lambda n, ctx: [
                    ctx.text(n.test).replace(".isupper()", "[1:].isupper()")
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_len_one_disjunct",
                match=lambda n, ctx: isinstance(n, ast.BoolOp)
                and isinstance(n.op, ast.Or)
                and any(_is_isupper_call(v) for v in n.values)
                and not any(
                    isinstance(v, ast.Compare)
                    and isinstance(v.left, ast.Call)
                    and isinstance(v.left.func, ast.Name)
                    and v.left.func.id == "len"
                    for v in n.values
                ),
                replace=lambda n, ctx: [ctx.text(n) + " or len(s) == 1"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_call_on_isupper_attribute",
                match=lambda n, ctx: _is_isupper_attr(n),
                replace=lambda n, ctx: [ctx.text(n) + "()"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="missing_call_on_islower_attribute",
                match=lambda n, ctx: _is_islower_call(n) is False
                and isinstance(n, ast.Attribute)
                and n.attr == "islower",
                replace=lambda n, ctx: [ctx.text(n) + "()"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="replace_title_with_swapcase_expression",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "title"
                and len(n.args) == 0,
                replace=lambda n, ctx: [ctx.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_capitalize_with_swapcase_expression",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "capitalize"
                and len(n.args) == 0,
                replace=lambda n, ctx: [ctx.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="uppercase_slice_compare_to_isupper",
                match=lambda n, ctx: _is_upper_slice_compare(n),
                replace=lambda n, ctx: [
                    ctx.text(n.left.value)
                    + "[1:].upper() == "
                    + ctx.text(n.left.value)
                    + "[1:]"
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_if_all_rest_upper",
                match=lambda n, ctx: isinstance(n, ast.If)
                and isinstance(n.test, ast.Compare)
                and isinstance(n.test.left, ast.Subscript),
                replace=lambda n, ctx: [
                    ctx.text(n).replace("capitalize()", "swapcase()").replace(
                        "title()", "swapcase()"
                    )
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_without_else_becomes_print_original",
                match=lambda n, ctx: isinstance(n, ast.If)
                and len(n.orelse) == 0
                and any(
                    isinstance(stmt, ast.Expr)
                    and isinstance(stmt.value, ast.Call)
                    and isinstance(stmt.value.func, ast.Name)
                    and stmt.value.func.id == "print"
                    for stmt in n.body
                ),
                replace=lambda n, ctx: [ctx.text(n) + "\nelse:\n    print(s)"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_start_off_by_one",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name)
                and n.func.id == "range"
                and len(n.args) == 2
                and isinstance(n.args[0], ast.Constant)
                and n.args[0].value == 0,
                replace=lambda n, ctx: ["range(1, " + ctx.text(n.args[1]) + ")"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="single_char_swapcase_branch",
                match=lambda n, ctx: isinstance(n, ast.If)
                and isinstance(n.test, ast.Compare)
                and any(
                    isinstance(op, ast.Eq)
                    for op in getattr(n.test, "ops", [])
                )
                and any(
                    isinstance(c, ast.Constant) and c.value == 1
                    for c in [n.test.left] + list(n.test.comparators)
                ),
                replace=lambda n, ctx: [ctx.text(n).replace(".lower()", ".swapcase()")],
                symptoms=("wrong",),
            ),
        ]