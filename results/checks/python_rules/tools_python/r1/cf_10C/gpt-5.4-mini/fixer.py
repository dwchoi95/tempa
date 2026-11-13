from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and not node.args
        and not node.keywords
    )


def _is_int_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0])
        and not node.keywords
    )


def _replace_input_with_int_input(node, ctx):
    return ["int(input())"]


def _is_string_len_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "len"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "str"
        and len(node.args[0].args) == 1
        and _is_input_call(node.args[0].args[0])
        and not node.keywords
    )


def _replace_string_len_input(node, ctx):
    return ["int(input())"]


def _is_while_len_str_ne_1(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and isinstance(node.test.left, ast.Call)
        and isinstance(node.test.left.func, ast.Name)
        and node.test.left.func.id == "len"
        and len(node.test.left.args) == 1
        and isinstance(node.test.left.args[0], ast.Call)
        and isinstance(node.test.left.args[0].func, ast.Name)
        and node.test.left.args[0].func.id == "str"
        and isinstance(node.test.ops[0], ast.NotEq)
        and len(node.test.comparators) == 1
        and isinstance(node.test.comparators[0], ast.Constant)
        and node.test.comparators[0].value == 1
    )


def _replace_while_len_str_ne_1(node, ctx):
    return [ctx.text(node).replace("len(str(n))!=1", "n>9").replace("len(str(n)) != 1", "n > 9")]


def _is_range_1_to_n_inclusive(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[1], ast.Name)
    )


def _replace_range_1_to_n_inclusive(node, ctx):
    return ["range(1, " + ctx.text(node.args[1]) + " + 1)"]


def _is_range_1_to_n_plus_1(node, ctx):
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


def _replace_range_1_to_n_plus_1(node, ctx):
    return ["range(1, " + ctx.text(node.args[1].left) + " + 1)"]


def _is_range_start_0_n(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 0
        and isinstance(node.args[1], ast.Constant)
        and node.args[1].value == 9
    )


def _replace_range_start_0_n(node, ctx):
    return ["range(1, 10)"]


def _is_eq_to_ne(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)


def _replace_eq_to_ne(node, ctx):
    return [ctx.text(node.left) + " != " + ctx.text(node.comparators[0])]


def _is_ne_to_eq(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.NotEq)


def _replace_ne_to_eq(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _is_lt_to_lte(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_gt_to_gte(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _replace_gt_to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_add_two_on_counter(node, ctx):
    return (
        isinstance(node, ast.AugAssign)
        and isinstance(node.op, ast.Add)
        and isinstance(node.value, ast.Constant)
        and node.value.value == 2
    )


def _replace_add_two_on_counter(node, ctx):
    return [ctx.text(node.target) + " += 1"]


def _is_append_zero(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Constant)
        and node.value.args[0].value == 0
    )


def _replace_append_zero(node, ctx):
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_should_be_converted_to_int",
                match=_is_string_len_input,
                replace=_replace_string_len_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="missing_int_around_input",
                match=_is_int_input,
                replace=_replace_input_with_int_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="while_len_str_not_one_to_digit_test",
                match=_is_while_len_str_ne_1,
                replace=_replace_while_len_str_ne_1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_1_to_n_inclusive",
                match=_is_range_1_to_n_inclusive,
                replace=_replace_range_1_to_n_inclusive,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_1_to_n_plus_one_off_by_one",
                match=_is_range_1_to_n_plus_1,
                replace=_replace_range_1_to_n_plus_1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_zero_to_n_should_start_at_one",
                match=_is_range_start_0_n,
                replace=_replace_range_start_0_n,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="eq_should_be_ne",
                match=_is_eq_to_ne,
                replace=_replace_eq_to_ne,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ne_should_be_eq",
                match=_is_ne_to_eq,
                replace=_replace_ne_to_eq,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lt_should_be_lte",
                match=_is_lt_to_lte,
                replace=_replace_lt_to_lte,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="gt_should_be_gte",
                match=_is_gt_to_gte,
                replace=_replace_gt_to_gte,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="increment_by_two_should_be_one",
                match=_is_add_two_on_counter,
                replace=_replace_add_two_on_counter,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="remove_zero_append_placeholder",
                match=_is_append_zero,
                replace=_replace_append_zero,
                symptoms=("wrong",),
            ),
        ]