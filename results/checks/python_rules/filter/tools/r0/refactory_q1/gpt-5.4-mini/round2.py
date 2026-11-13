from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_seq_check_none(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp)
        and isinstance(node.test.op, ast.Or)
        and any(isinstance(v, ast.Compare) and any(isinstance(op, (ast.Eq, ast.Is)) for op in v.ops) for v in node.test.values)
        and any(
            (isinstance(v, ast.Constant) and v.value is None)
            or (isinstance(v, ast.Tuple) and len(v.elts) == 0)
            or (isinstance(v, ast.List) and len(v.elts) == 0)
            for v in node.body
            if isinstance(v, ast.Return)
        )
    )


def _replace_none_with_zero(node, ctx):
    return ["if " + ctx.text(node.test) + ":\n    return 0"]


def _is_lenseq_pass(node, ctx):
    return isinstance(node, ast.If) and isinstance(node.test, ast.Compare) and "len(" in ctx.text(node.test) and any(isinstance(s, ast.Pass) for s in node.body)


def _replace_pass_return_zero(node, ctx):
    return [ctx.text(node.test) + ":\n    return 0"]


def _is_return_i_plus_one(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add) and isinstance(node.value.left, ast.Name) and isinstance(node.value.right, ast.Constant) and node.value.right.value == 1


def _replace_plus_one_len(node, ctx):
    return ["return len(seq)"]


def _is_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_return_none_len(node, ctx):
    p = ctx.parent(node)
    if isinstance(p, ast.If):
        return ["return len(seq)"]
    return []


def _is_for_break_return(node, ctx):
    return isinstance(node, ast.For) and any(isinstance(s, ast.Return) for s in node.body) and any(
        isinstance(s, ast.Return) and s.value is not None and isinstance(s.value, ast.Name) and s.value.id == "i"
        for s in node.body
    )


def _replace_for_break_return(node, ctx):
    return [ctx.text(node).replace("\n        return i", "\n        continue") + "\n    return len(seq)"]


def _is_while_double_step(node, ctx):
    return isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add) and isinstance(node.value, ast.Name) and node.value.id == "position"


def _replace_double_step(node, ctx):
    return [ctx.text(node.target) + " += 1"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_seq_return_none_should_return_zero", match=_is_empty_seq_check_none, replace=_replace_none_with_zero, symptoms=("wrong",)),
            Rewrite(name="pass_on_len_zero_should_return_zero", match=_is_lenseq_pass, replace=_replace_pass_return_zero, symptoms=("wrong",)),
            Rewrite(name="return_i_plus_one_should_be_len_seq", match=_is_return_i_plus_one, replace=_replace_plus_one_len, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt_compare, replace=_replace_lt_to_lte, symptoms=("wrong",)),
            Rewrite(name="bare_return_none_should_return_len_seq", match=_is_return_none, replace=_replace_return_none_len, symptoms=("wrong",)),
            Rewrite(name="for_loop_return_should_continue_then_fallthrough", match=_is_for_break_return, replace=_replace_for_break_return, symptoms=("wrong",)),
            Rewrite(name="position_doubled_should_increment_by_one", match=_is_while_double_step, replace=_replace_double_step, symptoms=("wrong",)),
        ]