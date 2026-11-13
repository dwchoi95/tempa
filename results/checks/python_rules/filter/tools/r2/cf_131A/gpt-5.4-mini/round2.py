from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
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


def _is_swapcase_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "swapcase"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_upper_on_slice(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "upper"
        and len(node.args) == 0
        and len(node.keywords) == 0
        and isinstance(node.func.value, ast.Subscript)
    )


def _is_upper_compare_slice(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (_is_upper_on_slice(node.left, ctx) and ctx.text(node.comparators[0]) == ctx.text(node.left.func.value))
            or (_is_upper_on_slice(node.comparators[0], ctx) and ctx.text(node.left) == ctx.text(node.comparators[0].func.value))
        )
    )


def _replace_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _fix_title_on_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _fix_upper_slice_compare(node, ctx):
    return [ctx.text(node.left.func.value) + "[1:] == " + ctx.text(node.left.func.value) + "[1:].upper()"]


def _fix_upper_slice_truthy(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.left) + ".upper()"]


def _fix_isupper_attr(node, ctx):
    return [ctx.text(node.func.value) + ".isupper()"]


def _fix_islower_attr(node, ctx):
    return [ctx.text(node.func.value) + ".islower()"]


def _fix_capitalize(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _fix_title(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


def _fix_len_one_or_upper_slice(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.left) + ".upper()"]


def _fix_bad_or_to_and(node, ctx):
    return [ctx.text(node.left) + " and " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="missing_isupper_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "isupper",
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_islower_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "islower",
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="upper_slice_truthy_check_to_equality",
                match=lambda n, c: isinstance(n, ast.Attribute)
                and n.attr == "upper"
                and isinstance(n.value, ast.Subscript)
                and isinstance(c.parent(n), ast.Compare),
                replace=lambda n, c: [c.text(n.func.value) + " == " + c.text(n) + "()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="isupper_slice_compare_should_use_slice_equality",
                match=_is_upper_compare_slice,
                replace=_fix_upper_slice_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="always_truthy_upper_method_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "upper" and isinstance(c.parent(n), ast.BoolOp),
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="capitalize_should_be_swapcase_in_capslock_solution",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in {"capitalize", "title"}
                and len(n.args) == 0
                and len(n.keywords) == 0,
                replace=lambda n, c: [c.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_solution_missing_one_branch",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.BoolOp)
                and any(isinstance(v, ast.Compare) and isinstance(v.ops[0], ast.Or) for v in []),
                replace=lambda n, c: [],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_over_capitalize_branch",
                match=lambda n, c: _is_swapcase_call(n, c) and isinstance(c.parent(n), ast.Assign),
                replace=_replace_swapcase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_one_and_should_be_or",
                match=lambda n, c: isinstance(n, ast.BoolOp)
                and isinstance(n.op, ast.And)
                and any(isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq) for v in n.values),
                replace=lambda n, c: [
                    " or ".join(c.text(v) for v in n.values)
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_one_special_case_missing_or_branch",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.Gt)
                and isinstance(n.left, ast.Call)
                and isinstance(n.left.func, ast.Name)
                and n.left.func.id == "len",
                replace=lambda n, c: [c.text(n.left) + " >= " + c.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="boolean_method_missing_parentheses",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr in {"isupper", "islower"},
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_swapcase_instead_of_lower_or_title",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in {"lower", "title", "capitalize"}
                and len(n.args) == 0
                and len(n.keywords) == 0
                and (
                    (isinstance(c.parent(n), ast.Assign) and isinstance(c.parent(c.parent(n)), ast.If))
                    or isinstance(c.parent(n), ast.Return)
                    or isinstance(c.parent(n), ast.Expr)
                ),
                replace=lambda n, c: [c.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="or_on_caps_rule_should_be_and_for_slice_check",
                match=lambda n, c: isinstance(n, ast.BoolOp)
                and isinstance(n.op, ast.Or)
                and any(isinstance(v, ast.BoolOp) and isinstance(v.op, ast.And) for v in n.values),
                replace=lambda n, c: [c.text(n.values[0]) + " or " + c.text(n.values[-1])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="inverted_caps_lock_test",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.Name)
                and n.test.id in {"a", "s", "w", "word", "n", "x"},
                replace=lambda n, c: [],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_input_assignment_to_strip_only",
                match=lambda n, c: isinstance(n, ast.Assign)
                and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and _is_input_call(n.value),
                replace=lambda n, c: [c.text(n)],
                symptoms=("wrong",),
            ),
        ]