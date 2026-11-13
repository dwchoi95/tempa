from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_int_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
    )


def _is_count_lucky_digit_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.NotEq))
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7, "4", "7")
    )


def _fix_digit_compare(node, ctx):
    left = ctx.text(node.left)
    comp = node.comparators[0].value
    comp_text = repr(str(comp)) if isinstance(comp, int) else repr(comp)
    op = "==" if isinstance(node.ops[0], ast.Eq) else "!="
    return [f"{left} {op} {comp_text}"]


def _is_compare_to_both_4_7(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(
            isinstance(v, ast.Compare)
            and len(v.ops) == 1
            and isinstance(v.ops[0], ast.Eq)
            and len(v.comparators) == 1
            and isinstance(v.comparators[0], ast.Constant)
            and v.comparators[0].value in (4, 7, "4", "7")
            for v in node.values
        )
    )


def _fix_or_digits(node, ctx):
    vals = node.values
    pieces = []
    for v in vals:
        pieces.append(ctx.text(v.left) + " == " + repr(str(v.comparators[0].value)))
    return [" or ".join(pieces)]


def _is_count_incorrect_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Compare)
        and len(node.value.ops) == 1
        and isinstance(node.value.ops[0], ast.In)
        and isinstance(node.value.left, ast.Name)
        and len(node.value.comparators) == 1
        and isinstance(node.value.comparators[0], ast.Tuple)
        and len(node.value.comparators[0].elts) == 2
        and all(isinstance(e, ast.Constant) and e.value in (4, 7) for e in node.value.comparators[0].elts)
    )


def _fix_return_in(node, ctx):
    lhs = ctx.text(node.value.left)
    return [f"{lhs} in (4, 7)"]


def _is_count_eq_len(node, ctx):
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


def _fix_count_eq_len(node, ctx):
    return [f"{ctx.text(node.left)} == 4 or {ctx.text(node.left)} == 7"]


def _is_count_eq_or_literal(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7, "4", "7")
    )


def _fix_count_eq_literal(node, ctx):
    return [f"{ctx.text(node.left)} == 4 or {ctx.text(node.left)} == 7"]


def _is_wrong_any_all(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in ("all", "any")
        and len(node.args) == 1
        and isinstance(node.args[0], ast.GeneratorExp)
    )


def _fix_any_all(node, ctx):
    return ["sum(1 for c in input() if c in '47')"]


def _is_modulo_wrong(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Mod)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
    )


def _fix_modulo_wrong(node, ctx):
    return [f"{ctx.text(node.left.left)} % 10 == {ctx.text(node.comparators[0])}"]


def _is_wrong_lucky_count_test(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq) for v in node.values)
        and all(isinstance(v.comparators[0], ast.Constant) and v.comparators[0].value in (4, 7, "4", "7")
                for v in node.values if len(v.comparators) == 1)
    )


def _fix_lucky_count_test(node, ctx):
    left = ctx.text(node.values[0].left)
    return [f"{left} == 4 or {left} == 7"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="int_digit_compare_should_use_string_digit",
                match=lambda n, ctx: _is_count_lucky_digit_compare(n, ctx),
                replace=_fix_digit_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="or_of_digit_constants_should_be_string_digit_comparisons",
                match=lambda n, ctx: _is_compare_to_both_4_7(n, ctx),
                replace=_fix_or_digits,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_membership_on_count_should_compare_to_lucky_numbers",
                match=lambda n, ctx: _is_count_incorrect_return(n, ctx),
                replace=_fix_return_in,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_equals_len_should_compare_to_4_or_7",
                match=lambda n, ctx: _is_count_eq_len(n, ctx),
                replace=_fix_count_eq_len,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_equals_literal_should_compare_against_lucky_counts",
                match=lambda n, ctx: _is_count_eq_or_literal(n, ctx),
                replace=_fix_count_eq_literal,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_any_all_generator_for_lucky_digits",
                match=lambda n, ctx: _is_wrong_any_all(n, ctx),
                replace=_fix_any_all,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_modulo_digit_check",
                match=lambda n, ctx: _is_modulo_wrong(n, ctx),
                replace=_fix_modulo_wrong,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lucky_count_miscompared_as_or_chain",
                match=lambda n, ctx: _is_wrong_lucky_count_test(n, ctx),
                replace=_fix_lucky_count_test,
                symptoms=("wrong",),
            ),
        ]