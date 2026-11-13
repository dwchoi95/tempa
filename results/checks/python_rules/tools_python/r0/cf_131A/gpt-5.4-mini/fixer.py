from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_len_one_check(node, ctx):
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


def _is_isupper_attr(node):
    return isinstance(node, ast.Attribute) and node.attr == "isupper"


def _is_islower_attr(node):
    return isinstance(node, ast.Attribute) and node.attr == "islower"


def _is_isupper_call(node):
    return isinstance(node, ast.Call) and _is_isupper_attr(node.func) and len(node.args) == 0 and len(node.keywords) == 0


def _is_islower_call(node):
    return isinstance(node, ast.Call) and _is_islower_attr(node.func) and len(node.args) == 0 and len(node.keywords) == 0


def _invert_case_expr(text):
    return f"{text}.swapcase()"


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="capitalize_to_swapcase_for_capslock_check",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr in {"title", "capitalize", "istitle"},
                replace=lambda n, c: [c.text(n.func.value) + ".swapcase()"] if isinstance(n, ast.Call) else [],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_input_parentheses",
                match=lambda n, c: isinstance(n, ast.Attribute)
                and n.attr in {"isupper", "islower", "istitle"}
                and not isinstance(c.parent(n), ast.Call),
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="compare_slice_isupper_to_upper_equality",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.Eq)
                and isinstance(n.left, ast.Subscript)
                and isinstance(n.left.slice, ast.Slice)
                and isinstance(n.comparators[0], ast.Call)
                and isinstance(n.comparators[0].func, ast.Attribute)
                and n.comparators[0].func.attr == "upper"
                and len(n.comparators[0].args) == 0,
                replace=lambda n, c: [c.text(n.left) + ".upper() == " + c.text(n.left)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_one_should_use_or_with_caps_condition",
                match=lambda n, c: isinstance(n, ast.BoolOp)
                and isinstance(n.op, ast.And)
                and any(_is_len_one_check(v, c) for v in n.values),
                replace=lambda n, c: [
                    " or ".join(
                        [c.text(v) for v in n.values if not _is_len_one_check(v, c)]
                        + ["len(" + c.text(n.values[0].left.args[0]) + ") == 1"]
                        if n.values and isinstance(n.values[0], ast.Compare)
                        else [c.text(n)]
                    )
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_swapcase_instead_of_capitalize_on_capslock",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "capitalize",
                replace=lambda n, c: [c.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_swapcase_instead_of_lower_on_all_caps_branch",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "lower"
                and isinstance(c.parent(n), ast.Return)
                and isinstance(c.parent(c.parent(n)), ast.If),
                replace=lambda n, c: [c.text(n.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="index0_upper_branch_should_use_full_word_condition",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.Attribute)
                and isinstance(n.test.value, ast.Subscript)
                and isinstance(n.test.value.slice, ast.Constant)
                and n.test.value.slice.value == 0
                and n.test.attr == "isupper",
                replace=lambda n, c: [
                    c.text(n.test.value.value) + ".isupper()"
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="swapcase_missing_on_single_letter_branch",
                match=lambda n, c: isinstance(n, ast.If)
                and isinstance(n.test, ast.Compare)
                and isinstance(n.test.left, ast.Call)
                and isinstance(n.test.left.func, ast.Name)
                and n.test.left.func.id == "len"
                and any(isinstance(op, ast.Eq) for op in n.test.ops)
                and any(isinstance(comp, ast.Constant) and comp.value == 1 for comp in n.test.comparators),
                replace=lambda n, c: [c.text(n).replace(".capitalize()", ".swapcase()").replace(".upper()", ".swapcase()")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_capitalize_return_to_swapcase_return",
                match=lambda n, c: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr in {"capitalize", "title"},
                replace=lambda n, c: ["return " + c.text(n.value.func.value) + ".swapcase()"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_isupper_without_call",
                match=lambda n, c: isinstance(n, ast.Attribute)
                and n.attr == "isupper"
                and not isinstance(c.parent(n), ast.Call),
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="fix_islower_without_call",
                match=lambda n, c: isinstance(n, ast.Attribute)
                and n.attr == "islower"
                and not isinstance(c.parent(n), ast.Call),
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="slice_one_before_upper_check_to_full_suffix",
                match=lambda n, c: isinstance(n, ast.Subscript)
                and isinstance(n.slice, ast.Slice)
                and n.slice.lower is None
                and n.slice.upper is not None
                and isinstance(n.slice.upper, ast.Constant)
                and n.slice.upper.value == 1,
                replace=lambda n, c: [c.text(n.value) + "[1:]"],
                symptoms=("wrong",),
            ),
        ]