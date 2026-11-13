from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_small_binary_search_bound(node, ctx):
    """Catches `r = 100` (or similar) used as the upper bound of an
    integer binary search that should cover a much larger range."""
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    if not (isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, int)
            and node.value.value == 100):
        return False
    name = node.targets[0].id
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.While):
            cond = n.test
            if isinstance(cond, ast.Compare):
                for sub in ast.walk(cond):
                    if isinstance(sub, ast.Name) and sub.id == name:
                        return True
    return False


def _widen_binary_search_bound(node, ctx):
    tgt = ctx.text(node.targets[0])
    return [f"{tgt} = 100000"]


def _get_loop_iter_len_arg_name(node):
    it = node.iter
    if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
        if it.args:
            last = it.args[-1]
            if (isinstance(last, ast.Call) and isinstance(last.func, ast.Name)
                    and last.func.id == "len" and last.args
                    and isinstance(last.args[0], ast.Name)):
                return last.args[0].id
    return None


def _is_greedy_redistribution_loop(node, ctx):
    """Matches the misconception of trying to "flow" one unit of a
    participant from one food group to another inside nested loops,
    instead of just scanning possible day counts directly."""
    if not isinstance(node, ast.For):
        return False
    if _get_loop_iter_len_arg_name(node) is None:
        return False
    whiles = [n for n in ast.walk(node) if isinstance(n, ast.While)]
    if not whiles:
        return False
    sub_augs = [n for n in ast.walk(node)
                if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Subscript)]
    has_sub = any(isinstance(n.op, ast.Sub) for n in sub_augs)
    has_add = any(isinstance(n.op, ast.Add) for n in sub_augs)
    return has_sub and has_add


def _find_first_two_var_name(ctx):
    for stmt in ctx.tree.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            tgt = stmt.targets[0]
            if (isinstance(tgt, ast.Tuple) and len(tgt.elts) == 2
                    and all(isinstance(e, ast.Name) for e in tgt.elts)):
                return tgt.elts[0].id
    return "n"


def _find_answer_var_name(node, ctx):
    parent = ctx.parent(node)
    field = ctx.field(node)
    body = getattr(parent, field, None) if field else None
    if not isinstance(body, list):
        return None
    try:
        idx = body.index(node)
    except ValueError:
        return None
    for nxt in body[idx + 1:]:
        if isinstance(nxt, ast.Expr) and isinstance(nxt.value, ast.Call):
            call = nxt.value
            if (isinstance(call.func, ast.Name) and call.func.id == "print"
                    and call.args and isinstance(call.args[0], ast.Name)):
                return call.args[0].id
    return None


def _fix_greedy_redistribution_loop(node, ctx):
    food_name = _get_loop_iter_len_arg_name(node)
    if food_name is None:
        return []
    n_name = _find_first_two_var_name(ctx)
    prev_name = _find_answer_var_name(node, ctx)
    if prev_name is None:
        return []

    code = (
        f"{prev_name} = 0\n"
        f"for __i in range(100, 0, -1):\n"
        f"    __to = 0\n"
        f"    for __v in {food_name}:\n"
        f"        __to += __v // __i\n"
        f"    if __to >= {n_name}:\n"
        f"        {prev_name} = __i\n"
        f"        break"
    )
    return [code]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="widen_small_binary_search_bound",
                match=_is_small_binary_search_bound,
                replace=_widen_binary_search_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_greedy_flow_redistribution_with_direct_scan",
                match=_is_greedy_redistribution_loop,
                replace=_fix_greedy_redistribution_loop,
                symptoms=("wrong", "timeout"),
            ),
        ]