from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_search_call_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE))


def _fix_return_none(node, ctx):
    return ["0"]


def _fix_return_empty_tuple_or_str(node, ctx):
    return ["0"]


def _fix_return_str_len(node, ctx):
    return ["len(seq)"]


def _fix_return_minus_one(node, ctx):
    return ["count"]


def _fix_off_by_one_minus(node, ctx):
    return [ctx.text(node.left) + " + 1"]


def _fix_strict_to_nonstrict(node, ctx):
    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt):
        return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]
    return []


def _fix_strict_gt_to_ge(node, ctx):
    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt):
        return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]
    return []


def _fix_empty_check_seq_eq_tuple_list(node, ctx):
    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq):
        left = ctx.text(node.left)
        right = ctx.text(node.comparators[0])
        if right in ("()", "[]") or left == "seq == () or []":
            return ["len(seq) == 0"]
    return []


def _fix_seq_eq_or_empty(node, ctx):
    txt = ctx.text(node)
    if txt in ("seq == () or []", "seq == [] or ()", "seq==() or []", "seq==[]or()"):
        return ["len(seq) == 0"]
    return []


def _fix_return_in_loop(node, ctx):
    if isinstance(node, ast.Return):
        parent = ctx.parent(node)
        if isinstance(parent, ast.For):
            return [ctx.text(node)]
    return []


def _fix_index_return_i_minus_1(node, ctx):
    txt = ctx.text(node)
    if txt in ("i-1", "i - 1"):
        return ["i"]
    return []


def _fix_index_return_len_minus_1(node, ctx):
    txt = ctx.text(node)
    if txt in ("len(seq)-1", "len(seq) - 1"):
        return ["len(seq)"]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite("none_to_zero", _fix_return_none, _fix_return_none, symptoms=("wrong",)),
            Rewrite("empty_to_zero", _fix_return_empty_tuple_or_str, _fix_return_empty_tuple_or_str, symptoms=("wrong",)),
            Rewrite("len_minus_one_to_len", _fix_return_str_len, _fix_return_str_len, symptoms=("wrong",)),
            Rewrite("minus_one_to_count", _fix_return_minus_one, _fix_return_minus_one, symptoms=("wrong",)),
            Rewrite("strict_lt_to_lte", _fix_strict_to_nonstrict, _fix_strict_to_nonstrict, symptoms=("wrong",)),
            Rewrite("strict_gt_to_gte", _fix_strict_gt_to_ge, _fix_strict_gt_to_ge, symptoms=("wrong",)),
            Rewrite("empty_check_as_len_zero", _fix_seq_eq_or_empty, _fix_seq_eq_or_empty, symptoms=("wrong",)),
            Rewrite("return_inside_for_keep_searching", _fix_return_in_loop, _fix_return_in_loop, symptoms=("wrong",)),
            Rewrite("off_by_one_minus_to_identity", _fix_index_return_i_minus_1, _fix_index_return_i_minus_1, symptoms=("wrong",)),
            Rewrite("len_seq_minus_one_to_len_seq", _fix_index_return_len_minus_1, _fix_index_return_len_minus_1, symptoms=("wrong",)),
        ]