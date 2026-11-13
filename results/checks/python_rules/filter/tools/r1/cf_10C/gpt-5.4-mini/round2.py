from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_not_int(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and not node.args
        and not node.keywords
        and isinstance(ctx.parent(node), ast.Call)
        and isinstance(ctx.parent(node).func, ast.Name)
        and ctx.parent(node).func.id in {"int", "d", "root"}
    )


def _wrap_int(node, ctx):
    return [f"int({ctx.text(node)})"]


def _is_nonroot_digit_sum_basecase(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and isinstance(node.left, ast.Name)
        and node.left.id in {"x", "n", "num", "s"}
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 9
    )


def _to_lt_10(node, ctx):
    return [f"{ctx.text(node.left)} < 10"]


def _is_i_from_1_to_n_wrong(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Add)
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _fix_range_upper(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1].left)})"]


def _is_sum_digits_loop_base(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.comparators[0], ast.Constant)
        and node.test.comparators[0].value == 1
        and isinstance(node.test.left, ast.Call)
        and isinstance(node.test.left.func, ast.Name)
        and node.test.left.func.id == "len"
    )


def _fix_while_digits(node, ctx):
    test = ctx.text(node.test)
    body = "\n".join(ctx.text(s) for s in node.body)
    return [f"while {test}:\n{body}"]


def _is_print_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id in {"d", "root"}
        and len(node.args[0].args) == 1
        and isinstance(node.args[0].args[0], ast.Call)
        and isinstance(node.args[0].args[0].func, ast.Name)
        and node.args[0].args[0].func.id == "input"
    )


def _fix_print_input(node, ctx):
    return [f"print({ctx.text(node.args[0].func)}(int(input())))"]


def _is_loop_start_at_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) >= 1
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
    )


def _fix_range_start(node, ctx):
    if len(node.args) == 1:
        return [f"range(0, {ctx.text(node.args[0])})"]
    return [f"range(0, {', '.join(ctx.text(a) for a in node.args[1:])})"]


def _is_c_equals_product_count_guard(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp)
        and isinstance(node.test.op, ast.And)
        and len(node.test.values) == 2
    )


def _simplify_and_guard(node, ctx):
    a, b = node.test.values
    return [f"if {ctx.text(a)}:\n" + "\n".join(ctx.text(s) for s in node.body)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_should_be_converted_to_int",
                match=_is_input_not_int,
                replace=_wrap_int,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="digit_root_base_case_should_use_10",
                match=_is_nonroot_digit_sum_basecase,
                replace=_to_lt_10,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_should_be_exclusive_n_plus_one",
                match=_is_i_from_1_to_n_wrong,
                replace=_fix_range_upper,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_digit_sum_condition_stays_same_shape",
                match=_is_sum_digits_loop_base,
                replace=_fix_while_digits,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_of_nested_input_call_should_parse_input_as_int",
                match=_is_print_input,
                replace=_fix_print_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="range_start_should_include_zero_when_counting_buckets",
                match=_is_loop_start_at_one,
                replace=_fix_range_start,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="simplify_and_guard_to_first_condition",
                match=_is_c_equals_product_count_guard,
                replace=_simplify_and_guard,
                symptoms=("wrong",),
            ),
        ]