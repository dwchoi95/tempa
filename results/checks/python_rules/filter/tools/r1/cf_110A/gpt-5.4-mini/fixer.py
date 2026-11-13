from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_count_lucky_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.NotEq, ast.In, ast.NotIn, ast.Gt, ast.GtE, ast.Lt, ast.LtE))
        and (
            (isinstance(node.left, ast.Call)
             and isinstance(node.left.func, ast.Attribute)
             and node.left.func.attr == "count")
            or (isinstance(node.comparators[0], ast.Call)
                and isinstance(node.comparators[0].func, ast.Attribute)
                and node.comparators[0].func.attr == "count")
        )
    )


def _replace_count_lucky_compare(node, ctx):
    txt = ctx.text(node)
    if "== len(" in txt or "==len(" in txt:
        if isinstance(node.ops[0], ast.Eq):
            return [txt.replace("== len(", "in {").replace("==len(", "in {") + "}"]
    return []


def _is_count_eq_4_or_7(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq) for v in node.values)
    )


def _replace_count_eq_4_or_7(node, ctx):
    left = node.values[0]
    right = node.values[1]
    return [f"({ctx.text(left.left)} == 4 or {ctx.text(right.left)} == 7)"]


def _is_digit_compare_with_int(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (isinstance(node.left, ast.Subscript) and isinstance(node.comparators[0], ast.Constant) and isinstance(node.comparators[0].value, int))
            or (isinstance(node.comparators[0], ast.Subscript) and isinstance(node.left, ast.Constant) and isinstance(node.left.value, int))
        )
    )


def _replace_digit_compare_with_int(node, ctx):
    if isinstance(node.left, ast.Subscript):
        return [f"{ctx.text(node.left)} == '{ctx.text(node.comparators[0])}'"]
    return [f"{ctx.text(node.comparators[0])} == '{ctx.text(node.left)}'"]


def _is_lucky_digit_test(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq) for v in node.values)
    )


def _replace_lucky_digit_test(node, ctx):
    a, b = node.values
    return [f"({ctx.text(a.left)} == '4' or {ctx.text(b.left)} == '7')"]


def _is_len_equals_count(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == "len")
            or (isinstance(node.comparators[0], ast.Call) and isinstance(node.comparators[0].func, ast.Name) and node.comparators[0].func.id == "len")
        )
    )


def _replace_len_equals_count(node, ctx):
    return ["count in (4, 7)"]


def _is_mod4_or7_on_count(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq) for v in node.values)
        and any(isinstance(v.left, ast.BinOp) and isinstance(v.left.op, ast.Mod) for v in node.values)
    )


def _replace_mod4_or7_on_count(node, ctx):
    return ["count in (4, 7)"]


def _is_any_digit_only_check(node, ctx):
    return isinstance(node, ast.If) and any(
        isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name) and sub.func.id == "any"
        for sub in ast.walk(node.test)
    )


def _replace_any_digit_only_check(node, ctx):
    return ["if s.count('4') + s.count('7') in {4, 7}:\n    print('YES')\nelse:\n    print('NO')"]


def _is_wrong_and_or(node, ctx):
    return isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and any(
        isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Mod)
        for v in node.values
    )


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="count_equals_len_should_be_count_lucky_number",
                match=_is_count_lucky_compare,
                replace=_replace_count_lucky_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_eq_4_or_7",
                match=_is_count_eq_4_or_7,
                replace=_replace_count_eq_4_or_7,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="digit_compare_needs_string_literal",
                match=_is_digit_compare_with_int,
                replace=_replace_digit_compare_with_int,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lucky_digit_test_needs_char_literals",
                match=_is_lucky_digit_test,
                replace=_replace_lucky_digit_test,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="length_check_should_be_count_check",
                match=_is_len_equals_count,
                replace=_replace_len_equals_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="modulo_on_count_should_be_direct_membership",
                match=_is_mod4_or7_on_count,
                replace=_replace_mod4_or7_on_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="any_digit_only_check_to_counting",
                match=_is_any_digit_only_check,
                replace=_replace_any_digit_only_check,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_or_on_numeric_lucky_test",
                match=_is_wrong_and_or,
                replace=lambda node, ctx: [],
                symptoms=("wrong",),
            ),
        ]