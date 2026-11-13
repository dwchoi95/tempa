from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_small_bound_search(node, ctx):
    """
    Matches the classic binary-search-bounded-by-100 bug: the search upper
    bound `r` is initialized to 100, which is too small once answers can
    exceed 100 (e.g. m/n can be larger than 100 in edge cases, though in
    this particular task the bound is at most 100 -- some submissions
    nonetheless cap their search range too tightly, e.g. at 100 while
    using it as a day-count bound that should allow headroom).
    """
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    if node.targets[0].id != "r":
        return False
    if not isinstance(node.value, ast.Constant):
        return False
    if not isinstance(node.value.value, int):
        return False
    return node.value.value == 100


def _widen_bound(node, ctx):
    return [ctx.text(node.targets[0]) + " = 100000"]


def _is_greedy_swap_block(node, ctx):
    """
    Matches the mis-conceived 'greedily move one package's worth of
    participants between the two closest buckets' algorithm: a top-level
    `for j in range(1, len(X)):` loop whose body contains both a
    boolean-flag assignment (`good = False`) and a nested `while` loop
    that tries to shuffle counts between buckets. This whole approach is
    fundamentally the wrong algorithm for the problem (the correct one is
    a simple brute force / binary search over candidate day counts), so
    we replace just this `for` statement with the correct search, keeping
    everything else (parsing, the bucket-count list, the later `print`)
    untouched.
    """
    if not isinstance(node, ast.For):
        return False
    it = node.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range"):
        return False
    if len(it.args) != 2:
        return False
    first = it.args[0]
    if not (isinstance(first, ast.Constant) and first.value == 1):
        return False

    has_bool_flag = False
    has_while = False
    for sub in ast.walk(node):
        if isinstance(sub, ast.Assign):
            if (isinstance(sub.value, ast.Constant)
                    and sub.value.value is False):
                has_bool_flag = True
        if isinstance(sub, ast.While):
            has_while = True
    return has_bool_flag and has_while


def _find_n_var(ctx):
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.Assign):
            tgt = n.targets[0]
            if isinstance(tgt, ast.Tuple) and len(tgt.elts) >= 1:
                first = tgt.elts[0]
                if isinstance(first, ast.Name):
                    return first.id
    return "n"


def _find_target_var(node, ctx):
    parent = ctx.parent(node)
    field = ctx.field(node)
    body = getattr(parent, field, None)
    if isinstance(body, list) and node in body:
        idx = body.index(node)
        if idx + 1 < len(body):
            nxt = body[idx + 1]
            if (isinstance(nxt, ast.Expr) and isinstance(nxt.value, ast.Call)
                    and isinstance(nxt.value.func, ast.Name)
                    and nxt.value.func.id == "print"
                    and len(nxt.value.args) == 1
                    and isinstance(nxt.value.args[0], ast.Name)):
                return nxt.value.args[0].id
    return "prev_days"


def _replace_greedy_swap(node, ctx):
    it = node.iter
    second = it.args[1]
    if not (isinstance(second, ast.Call) and isinstance(second.func, ast.Name)
            and second.func.id == "len" and len(second.args) == 1):
        return []
    list_name = ctx.text(second.args[0])
    n_var = _find_n_var(ctx)
    target = _find_target_var(node, ctx)

    text = (
        f"{target} = 0\n"
        f"for __day in range(100, 0, -1):\n"
        f"    __total = 0\n"
        f"    for __cnt in {list_name}:\n"
        f"        __total += __cnt // __day\n"
        f"    if __total >= {n_var}:\n"
        f"        {target} = __day\n"
        f"        break"
    )
    return [text]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="widen_binary_search_upper_bound",
                match=_is_small_bound_search,
                replace=_widen_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_greedy_swap_with_bruteforce_search",
                match=_is_greedy_swap_block,
                replace=_replace_greedy_swap,
                symptoms=("wrong", "timeout"),
            ),
        ]