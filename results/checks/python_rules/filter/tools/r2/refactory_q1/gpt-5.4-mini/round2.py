from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_seq_name(node, ctx):
    return isinstance(node, ast.Name) and node.id == "seq"


def _is_empty_check(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    left = node.left
    right = node.comparators[0]
    return (
        (isinstance(left, ast.Name) and left.id == "seq" and isinstance(right, ast.Constant) and right.value in ((), [], tuple(), list()))
        or (isinstance(right, ast.Name) and right.id == "seq" and isinstance(left, ast.Constant) and left.value in ((), [], tuple(), list()))
    )


def _replace_none_or_empty_return(node, ctx):
    return ["0"]


def _replace_false_return(node, ctx):
    return ["0"]


def _replace_seq_empty_return(node, ctx):
    return ["0"]


def _match_return_none(node, ctx):
    return isinstance(node, ast.Return) and (
        node.value is None or (isinstance(node.value, ast.Constant) and node.value.value in (None, False, (), [], "empty", "not found"))
    )


def _match_return_seq(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "seq"


def _match_return_tuple_or_list(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, (ast.Tuple, ast.List)) and len(node.value.elts) == 1


def _match_bad_return_len_minus_one(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Sub) and isinstance(node.value.right, ast.Constant) and node.value.right.value == 1


def _replace_len(node, ctx):
    return [ctx.text(node.value.left)]


def _match_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _match_gte_to_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)


def _replace_gte_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _match_lte_to_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)


def _replace_lte_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _match_return_i_plus_one(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add) and isinstance(node.value.right, ast.Constant) and node.value.right.value == 1


def _replace_return_i_plus_one(node, ctx):
    return [ctx.text(node.value.left)]


def _match_break_return_inside_loop(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "i"


class Fixer:
    def rules(self):
        return [
            Rewrite("empty_sequence_returns_zero", _match_return_none, _replace_none_or_empty_return, symptoms=("wrong",)),
            Rewrite("return_seq_should_be_zero", _match_return_seq, _replace_seq_empty_return, symptoms=("wrong",)),
            Rewrite("empty_tuple_or_list_returns_zero", _match_return_tuple_or_list, _replace_false_return, symptoms=("wrong",)),
            Rewrite("strict_lt_should_be_lte", _match_strict_lt_compare, _replace_lt_to_lte, symptoms=("wrong",)),
            Rewrite("gte_should_be_gt", _match_gte_to_gt, _replace_gte_to_gt, symptoms=("wrong",)),
            Rewrite("lte_should_be_lt", _match_lte_to_lt, _replace_lte_to_lt, symptoms=("wrong",)),
            Rewrite("off_by_one_return_i_plus_one", _match_return_i_plus_one, _replace_return_i_plus_one, symptoms=("wrong",)),
            Rewrite("len_minus_one_should_be_len", _match_bad_return_len_minus_one, _replace_len, symptoms=("wrong",)),
        ]