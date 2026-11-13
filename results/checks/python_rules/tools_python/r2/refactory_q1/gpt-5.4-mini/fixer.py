from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.Is))
        and isinstance(node.comparators[0], (ast.Tuple, ast.List))
        and len(node.comparators[0].elts) == 0
        and (
            isinstance(node.left, ast.Name)
            or isinstance(node.left, ast.Call)
            or isinstance(node.left, ast.Attribute)
            or isinstance(node.left, ast.Subscript)
            or isinstance(node.left, ast.Constant)
        )
    )


def _replace_empty_check_with_not(node, ctx):
    return ["not " + ctx.text(node.left)]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_wrong_return_len_plus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.left, ast.Call)
        and isinstance(node.value.left.func, ast.Name)
        and node.value.left.func.id == "len"
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _fix_return_len_plus_one(node, ctx):
    return ["return " + ctx.text(node.value.left)]


def _is_wrong_return_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Sub)
        and isinstance(node.value.left, ast.Call)
        and isinstance(node.value.left.func, ast.Name)
        and node.value.left.func.id == "len"
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _fix_return_len_minus_one(node, ctx):
    return ["return " + ctx.text(node.value.left)]


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is not None and isinstance(node.value, ast.Constant) and node.value.value is None


def _fix_return_none(node, ctx):
    return ["return 0"]


def _is_return_missing(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_return_missing(node, ctx):
    return ["return 0"]


def _is_range_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Sub)
        and isinstance(node.args[0].left, ast.Call)
        and isinstance(node.args[0].left.func, ast.Name)
        and node.args[0].left.func.id == "len"
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 1
    )


def _fix_range_len_minus_one(node, ctx):
    return ["range(" + ctx.text(node.args[0].left) + ")"]


def _is_range_bare_len(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_range_bare_len(node, ctx):
    return ["range(len(" + ctx.text(node.args[0]) + "))"]


def _is_plus_one_return_after_loop(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
        and isinstance(node.value.left, ast.Name)
    )


def _fix_plus_one_return_after_loop(node, ctx):
    return ["return " + ctx.text(node.value.left)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_should_return_zero", match=_is_empty_check,
                    replace=_replace_empty_check_with_not, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt,
                    replace=_to_lte, symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_gte", match=_is_strict_gt,
                    replace=_to_gte, symptoms=("wrong",)),
            Rewrite(name="return_len_plus_one_should_return_len", match=_is_wrong_return_len_plus_one,
                    replace=_fix_return_len_plus_one, symptoms=("wrong",)),
            Rewrite(name="return_len_minus_one_should_return_len", match=_is_wrong_return_len_minus_one,
                    replace=_fix_return_len_minus_one, symptoms=("wrong",)),
            Rewrite(name="return_none_should_return_zero", match=_is_return_none,
                    replace=_fix_return_none, symptoms=("wrong",)),
            Rewrite(name="bare_return_should_return_zero", match=_is_return_missing,
                    replace=_fix_return_missing, symptoms=("wrong",)),
            Rewrite(name="range_len_minus_one_should_be_range_len", match=_is_range_len_minus_one,
                    replace=_fix_range_len_minus_one, symptoms=("wrong",)),
            Rewrite(name="range_bare_name_should_be_range_len_name", match=_is_range_bare_len,
                    replace=_fix_range_bare_len, symptoms=("wrong",)),
            Rewrite(name="return_plus_one_result_should_return_result", match=_is_plus_one_return_after_loop,
                    replace=_fix_plus_one_return_after_loop, symptoms=("wrong",)),
        ]