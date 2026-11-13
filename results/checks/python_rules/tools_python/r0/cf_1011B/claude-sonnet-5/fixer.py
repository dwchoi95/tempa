from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_small_binary_search_bound(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    target_name = node.targets[0].id
    val = node.value
    if not (isinstance(val, ast.Constant) and isinstance(val.value, int)
            and not isinstance(val.value, bool) and val.value == 100):
        return False
    found = False
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.While):
            test = n.test
            if isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.Gt):
                left = test.left
                if isinstance(left, ast.BinOp) and isinstance(left.op, ast.Sub):
                    names = set()
                    for sub in (left.left, left.right):
                        if isinstance(sub, ast.Name):
                            names.add(sub.id)
                    if target_name in names:
                        found = True
    return found


def _bump_binary_search_bound(node, ctx):
    name = node.targets[0].id
    return [name + " = 100000"]


def _food_name_from_for(node):
    it = node.iter
    if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
        args = it.args
        if len(args) == 2:
            first, second = args[0], args[1]
            if isinstance(first, ast.Constant) and first.value == 1:
                if isinstance(second, ast.Call) and isinstance(second.func, ast.Name) and second.func.id == "len":
                    if len(second.args) == 1 and isinstance(second.args[0], ast.Name):
                        return second.args[0].id
    return None


def _find_n_name(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Tuple):
            elts = node.targets[0].elts
            if len(elts) == 2 and all(isinstance(e, ast.Name) for e in elts):
                val = node.value
                if isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == "map":
                    return elts[0].id
    return None


def _find_result_name(node, ctx):
    parent = ctx.parent(node)
    body = getattr(parent, "body", None)
    if body is None:
        return None
    idx = None
    for i, stmt in enumerate(body):
        if stmt is node:
            idx = i
            break
    if idx is None:
        return None
    for stmt in body[idx + 1:]:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            call = stmt.value
            if isinstance(call.func, ast.Name) and call.func.id == "print":
                if len(call.args) == 1 and isinstance(call.args[0], ast.Name):
                    return call.args[0].id
    return None


def _is_greedy_swap_for(node, ctx):
    if not isinstance(node, ast.For):
        return False
    food_name = _food_name_from_for(node)
    if food_name is None:
        return False
    if not any(isinstance(n, ast.While) for n in ast.walk(node)):
        return False
    has_sub = False
    has_add = False
    for n in ast.walk(node):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Subscript):
            if isinstance(n.op, ast.Sub):
                has_sub = True
            if isinstance(n.op, ast.Add):
                has_add = True
    if not (has_sub and has_add):
        return False
    n_name = _find_n_name(ctx.tree)
    if n_name is None:
        return False
    result_name = _find_result_name(node, ctx)
    if result_name is None:
        return False
    return True


def _fix_greedy_swap_for(node, ctx):
    food_name = _food_name_from_for(node)
    n_name = _find_n_name(ctx.tree)
    result_name = _find_result_name(node, ctx)
    if food_name is None or n_name is None or result_name is None:
        return []
    stmts = [
        "__ans = 0",
        "for __lvl in range(100, 0, -1):",
        "    __to = 0",
        "    for __cnt in " + food_name + ":",
        "        __to += __cnt // __lvl",
        "    if __to >= " + n_name + ":",
        "        __ans = __lvl",
        "        break",
        result_name + " = __ans",
    ]
    return ["\n".join(stmts)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="binary_search_bound_too_small",
                match=_is_small_binary_search_bound,
                replace=_bump_binary_search_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unsound_greedy_bucket_swap",
                match=_is_greedy_swap_for,
                replace=_fix_greedy_swap_for,
                symptoms=("wrong", "timeout"),
            ),
        ]