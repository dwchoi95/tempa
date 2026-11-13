from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_seq_test(node):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.Is))
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], (ast.List, ast.Tuple))
        and len(node.comparators[0].elts) == 0
    )


def _match_none_return_for_empty(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    p = ctx.parent(node)
    if not isinstance(p, ast.If):
        return False
    return _is_empty_seq_test(p.test)


def _replace_none_with_zero(node, ctx):
    return ["return 0"]


def _match_off_by_one_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_len_plus_one(node, ctx):
    left = node.value.left
    if isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == "len":
        return [f"return {ctx.text(left)}"]
    return []


def _match_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lt_to_lte(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _match_strict_gt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _replace_gt_to_gte(node, ctx):
    return [f"{ctx.text(node.left)} >= {ctx.text(node.comparators[0])}"]


def _match_wrong_index_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Name)
        and node.value.id in {"x", "elem", "element", "value"}
    )


def _replace_name_return_with_index(node, ctx):
    p = ctx.parent(node)
    if isinstance(p, ast.If):
        return [f"return {ctx.text(node.value)}"]
    return []


def _match_break_in_loop_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is None


def _replace_breaklike_return(node, ctx):
    return ["break"]


def _match_range_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Sub)
        and isinstance(node.args[0].args[0], ast.Call)
        and isinstance(node.args[0].args[0].func, ast.Name)
        and node.args[0].args[0].func.id == "len"
        and isinstance(node.args[0].args[1], ast.Constant)
        and node.args[0].args[1].value == 1
    )


def _replace_range_len_minus_one(node, ctx):
    return [f"range({ctx.text(node.args[0].args[0])})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_should_return_zero", match=_match_none_return_for_empty, replace=_replace_none_with_zero, symptoms=("wrong",)),
            Rewrite(name="len_plus_one_return_should_be_len", match=_match_off_by_one_return, replace=_replace_len_plus_one, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_match_strict_lt_compare, replace=_replace_lt_to_lte, symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_gte", match=_match_strict_gt_compare, replace=_replace_gt_to_gte, symptoms=("wrong",)),
            Rewrite(name="range_len_minus_one_should_be_range_len", match=_match_range_len_minus_one, replace=_replace_range_len_minus_one, symptoms=("wrong",)),
        ]