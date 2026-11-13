from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_digit_root_func(func_def):
    for n in ast.walk(func_def):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ("str", "int"):
            return True
    return False


def _assign_increment_target(stmt):
    if isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name) and isinstance(stmt.op, ast.Add):
        return stmt.target.id
    if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
        tgt = stmt.targets[0].id
        val = stmt.value
        if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
            if (isinstance(val.left, ast.Name) and val.left.id == tgt) or \
               (isinstance(val.right, ast.Name) and val.right.id == tgt):
                return tgt
    return None


def _find_counter_var(node):
    for sub in ast.walk(node):
        if isinstance(sub, ast.If):
            for stmt in sub.body:
                name = _assign_increment_target(stmt)
                if name:
                    return name
    return None


_FORMULA = """_q, _r = divmod(n, 9)
_droot = [_q] + [_q + 1] * _r + [_q] * (8 - _r)
_res = 0
for _i in range(9):
    for _j in range(9):
        _res += _droot[_i] * _droot[_j] * _droot[(_i * _j) % 9]
for _k in range(1, n + 1):
    _res -= n // _k"""


def _is_counting_double_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return False
    if not isinstance(node.target, ast.Name):
        return False
    inner_fors = [n for n in ast.walk(node) if isinstance(n, ast.For) and n is not node]
    if not inner_fors:
        return False
    return _find_counter_var(node) is not None


def _fix_counting_double_loop(node, ctx):
    target = _find_counter_var(node)
    if target is None:
        return []
    code = _FORMULA + "\n" + target + " = _res"
    return [code]


def _is_building_double_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return False
    if _find_counter_var(node) is not None:
        return False
    inner_fors = [n for n in ast.walk(node) if isinstance(n, ast.For) and n is not node]
    if not inner_fors:
        return False
    func_names = {f.name for f in ctx.tree.body if isinstance(f, ast.FunctionDef)}
    if not func_names:
        return False
    for sub in ast.walk(node):
        if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name) and sub.func.id in func_names:
            return True
    return False


def _delete_building_double_loop(node, ctx):
    return [""]


def _is_raw_digit_root_print(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not (isinstance(call.func, ast.Name) and call.func.id == "print"):
        return False
    if len(call.args) != 1:
        return False
    inner = call.args[0]
    if not (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name)):
        return False
    func_name = inner.func.id
    func_defs = {f.name: f for f in ctx.tree.body if isinstance(f, ast.FunctionDef)}
    if func_name not in func_defs or not _is_digit_root_func(func_defs[func_name]):
        return False
    if len(inner.args) != 1:
        return False
    arg = inner.args[0]
    if not (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == "input"):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return False
    return True


def _fix_raw_digit_root_print(node, ctx):
    code = "n = int(input())\n" + _FORMULA + "\nprint(_res)"
    return [code]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="bruteforce_counting_loop_to_digitroot_formula",
                match=_is_counting_double_loop,
                replace=_fix_counting_double_loop,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="drop_bruteforce_building_loop",
                match=_is_building_double_loop,
                replace=_delete_building_double_loop,
                symptoms=("timeout", "wrong"),
            ),
            Rewrite(
                name="raw_digit_root_print_to_formula",
                match=_is_raw_digit_root_print,
                replace=_fix_raw_digit_root_print,
                symptoms=("wrong", "timeout"),
            ),
        ]