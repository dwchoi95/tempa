from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_lucky_digit_compare(node):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.ops[0], ast.Eq)
    )


def _match_digit_char_vs_int(node, ctx):
    if not _is_lucky_digit_compare(node):
        return False
    left, right = node.left, node.comparators[0]
    return (
        (isinstance(left, ast.Name) and isinstance(right, ast.Constant) and isinstance(right.value, int))
        or (isinstance(right, ast.Name) and isinstance(left, ast.Constant) and isinstance(left.value, int))
        or (isinstance(left, ast.Subscript) and isinstance(right, ast.Constant) and isinstance(right.value, int))
        or (isinstance(right, ast.Subscript) and isinstance(left, ast.Constant) and isinstance(left.value, int))
    )


def _fix_digit_char_vs_int(node, ctx):
    if isinstance(node.left, (ast.Name, ast.Subscript)) and isinstance(node.comparators[0], ast.Constant):
        return [ctx.text(node.left) + " == '" + str(node.comparators[0].value) + "'"]
    if isinstance(node.comparators[0], (ast.Name, ast.Subscript)) and isinstance(node.left, ast.Constant):
        return [ctx.text(node.comparators[0]) + " == '" + str(node.left.value) + "'"]
    return []


def _match_count_eq_4_or_7(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 3
        and all(isinstance(op, ast.Eq) for op in node.ops)
        and all(isinstance(c, ast.Constant) and isinstance(c.value, int) for c in [node.left] + node.comparators)
        and node.left.value in (4, 7)
    )


def _fix_count_eq_4_or_7(node, ctx):
    expr = ctx.text(node.left)
    return [f"{expr} in (4, 7)"]


def _match_wrong_or_chain(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) for v in node.values)
    )


def _fix_wrong_or_chain(node, ctx):
    a, b = node.values
    if isinstance(a.ops[0], ast.Eq) and isinstance(b.ops[0], ast.Eq):
        return [f"({ctx.text(a.left)} == {ctx.text(a.comparators[0])} or {ctx.text(b.left)} == {ctx.text(b.comparators[0])})"]
    return []


def _match_count_digits_len(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Name)
        and node.comparators[0].func.id == "len"
    )


def _fix_count_digits_len(node, ctx):
    return [ctx.text(node.left) + " in (4, 7)"]


def _match_modulo_lucky(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Mod)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value in (4, 7)
    )


def _fix_modulo_lucky(node, ctx):
    return [ctx.text(node.left.left) + " in (4, 7)"]


def _match_count_var_in_lucky(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.In)
        and isinstance(node.comparators[0], (ast.Tuple, ast.List, ast.Set))
        and all(isinstance(e, ast.Constant) and e.value in (4, 7) for e in node.comparators[0].elts)
    )


def _fix_count_var_in_lucky(node, ctx):
    return [ctx.text(node.left) + " == 4 or " + ctx.text(node.left) + " == 7"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="digit_char_comparison_needs_quotes",
                match=_match_digit_char_vs_int,
                replace=_fix_digit_char_vs_int,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_equal_4_or_7_should_use_membership",
                match=_match_count_eq_4_or_7,
                replace=_fix_count_eq_4_or_7,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="or_chain_of_digit_equals",
                match=_match_wrong_or_chain,
                replace=_fix_wrong_or_chain,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_count_to_len_is_wrong",
                match=_match_count_digits_len,
                replace=_fix_count_digits_len,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="modulo_digit_test_is_wrong_for_count",
                match=_match_modulo_lucky,
                replace=_fix_modulo_lucky,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lucky_count_membership_expanded",
                match=_match_count_var_in_lucky,
                replace=_fix_count_var_in_lucky,
                symptoms=("wrong",),
            ),
        ]