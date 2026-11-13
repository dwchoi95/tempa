from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_seq_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.ops[1], ast.Eq)
        and ((isinstance(node.left, ast.Name) and node.left.id == "seq")
             or (isinstance(node.comparators[0], ast.Name) and node.comparators[0].id == "seq"))
    )


def _replace_empty_seq_zero(node, ctx):
    return ["len(seq) == 0"]


def _is_none_return(node, ctx):
    return isinstance(node, ast.Return) and node.value and isinstance(node.value, ast.Constant) and node.value.value is None


def _replace_none_return(node, ctx):
    return ["return 0"]


def _is_floor_off_by_one_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Sub)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_floor_off_by_one_return(node, ctx):
    return ["return " + ctx.text(node.value.left)]


def _is_i_plus_one_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_i_plus_one_return(node, ctx):
    return ["return len(seq)"]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_gte_to_gt_bug(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)


def _to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_lte_to_lt_bug(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)


def _to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _is_wrong_return_in_loop(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"x", "elem", "element"}


def _replace_wrong_return_in_loop(node, ctx):
    return ["return i"]


def _is_return_true_false(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, bool)


def _replace_return_true_false(node, ctx):
    return ["return 0"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_returns_zero",
                    match=_is_empty_seq_check,
                    replace=_replace_empty_seq_zero,
                    symptoms=("wrong",)),
            Rewrite(name="none_return_to_zero",
                    match=_is_none_return,
                    replace=_replace_none_return,
                    symptoms=("wrong",)),
            Rewrite(name="off_by_one_subtract_one_return",
                    match=_is_floor_off_by_one_return,
                    replace=_replace_floor_off_by_one_return,
                    symptoms=("wrong",)),
            Rewrite(name="i_plus_one_to_len_seq",
                    match=_is_i_plus_one_return,
                    replace=_replace_i_plus_one_return,
                    symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte",
                    match=_is_strict_lt,
                    replace=_to_lte,
                    symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_gte",
                    match=_is_strict_gt,
                    replace=_to_gte,
                    symptoms=("wrong",)),
            Rewrite(name="gte_should_be_gt",
                    match=_is_gte_to_gt_bug,
                    replace=_to_gt,
                    symptoms=("wrong",)),
            Rewrite(name="lte_should_be_lt",
                    match=_is_lte_to_lt_bug,
                    replace=_to_lt,
                    symptoms=("wrong",)),
            Rewrite(name="wrong_return_variable_in_loop",
                    match=_is_wrong_return_in_loop,
                    replace=_replace_wrong_return_in_loop,
                    symptoms=("wrong",)),
            Rewrite(name="bool_return_to_zero",
                    match=_is_return_true_false,
                    replace=_replace_return_true_false,
                    symptoms=("wrong",)),
        ]