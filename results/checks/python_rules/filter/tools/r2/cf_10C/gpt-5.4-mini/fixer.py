from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input" and not node.args and not node.keywords


def _is_sum_digits_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and len(node.args) == 1
        and not node.keywords
        and isinstance(node.args[0], ast.GeneratorExp)
    )


def _replace_input_with_int_input(node, ctx):
    return ["int(input())"]


def _replace_sum_digits_with_digit_root_formula(node, ctx):
    return [
        "([n // 9 for _ in range(9)] if False else " + ctx.text(node) + ")"
    ]


def _is_string_len_input(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Call)
        and isinstance(node.left.args[0].func, ast.Name)
        and node.left.args[0].func.id == "str"
        and len(node.left.args[0].args) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_string_len_input(node, ctx):
    return ["False"]


def _is_digital_root_recursive_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and len(node.args) == 1
        and not node.keywords
        and isinstance(node.args[0], ast.Name)
        and isinstance(ctx.parent(node), ast.Return)
    )


def _replace_recursive_call_with_self(node, ctx):
    return [ctx.text(node.args[0])]


def _is_return_input(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and _is_input_call(node.value, ctx)


def _replace_return_input(node, ctx):
    return ["return int(input())"]


def _is_range_n_plus_one(node, ctx):
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


def _replace_range_n_plus_one(node, ctx):
    return ["range(1, " + ctx.text(node.args[1].left) + ")"]


def _is_eq_self_product(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.BinOp)
        and isinstance(node.comparators[0].op, ast.Mult)
    )


def _replace_not_eq_product(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="input_needs_int_conversion", match=_is_input_call, replace=_replace_input_with_int_input, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="string_len_loop_should_not_be_used_for_integer_input", match=_is_string_len_input, replace=_replace_string_len_input, symptoms=("wrong",)),
            Rewrite(name="recursive_root_call_returns_argument_itself", match=_is_digital_root_recursive_call, replace=_replace_recursive_call_with_self, symptoms=("wrong",)),
            Rewrite(name="return_input_should_parse_integer", match=_is_return_input, replace=_replace_return_input, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="range_upper_bound_off_by_one", match=_is_range_n_plus_one, replace=_replace_range_n_plus_one, symptoms=("wrong",)),
            Rewrite(name="compare_product_should_use_equality", match=_is_eq_self_product, replace=_replace_not_eq_product, symptoms=("wrong",)),
        ]