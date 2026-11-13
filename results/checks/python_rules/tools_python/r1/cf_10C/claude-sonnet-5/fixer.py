from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _find_n_var(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            val = node.value
            if isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == 'int':
                if len(val.args) == 1 and isinstance(val.args[0], ast.Call):
                    inner = val.args[0]
                    if isinstance(inner.func, ast.Name) and inner.func.id == 'input':
                        return node.targets[0].id
    return 'n'


def _find_final_print_var(tree):
    last = None
    for node in tree.body:
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            call = node.value
            if isinstance(call.func, ast.Name) and call.func.id == 'print':
                if len(call.args) == 1 and isinstance(call.args[0], ast.Name):
                    last = call.args[0].id
    return last


def _formula_text(target, N):
    return (
        "q,r = divmod({N},9)\n"
        "_dr = [q]+[q+1]*r+[q]*(8-r)\n"
        "{T} = 0\n"
        "for _i in range(9):\n"
        "    for _j in range(9):\n"
        "        {T} += _dr[_i]*_dr[_j]*_dr[(_i*_j)%9]\n"
        "for _k in range(1,{N}+1):\n"
        "    {T} -= {N}//_k\n"
    ).format(T=target, N=N)


def _is_trivial_digitroot_print(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return False
    call = node.value
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == 'print'):
        return False
    if len(call.args) != 1 or not isinstance(call.args[0], ast.Call):
        return False
    tree = ctx.tree
    for n in ast.walk(tree):
        if isinstance(n, (ast.For, ast.While)):
            return False
    for stmt in tree.body:
        if stmt is node:
            continue
        if not isinstance(stmt, ast.FunctionDef):
            return False
    return True


def _replace_trivial_digitroot_print(node, ctx):
    text = (
        "n = int(input())\n"
        "q,r = divmod(n,9)\n"
        "_dr = [q]+[q+1]*r+[q]*(8-r)\n"
        "res = 0\n"
        "for _i in range(9):\n"
        "    for _j in range(9):\n"
        "        res += _dr[_i]*_dr[_j]*_dr[(_i*_j)%9]\n"
        "for _k in range(1,n+1):\n"
        "    res -= n//_k\n"
        "print(res)"
    )
    return [text]


def _find_counter_var(stmts):
    for stmt in stmts:
        for n in ast.walk(stmt):
            if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and isinstance(n.op, ast.Add):
                return n.target.id
            if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
                val = n.value
                if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
                    if isinstance(val.left, ast.Name) and val.left.id == n.targets[0].id:
                        return n.targets[0].id
    return None


def _is_bruteforce_counter_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if not isinstance(ctx.parent(node), ast.Module):
        return False
    if not (isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range'):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.For):
        return False
    inner = node.body[0]
    if not (isinstance(inner.iter, ast.Call) and isinstance(inner.iter.func, ast.Name) and inner.iter.func.id == 'range'):
        return False
    return _find_counter_var(inner.body) is not None


def _replace_bruteforce_counter_loop(node, ctx):
    inner = node.body[0]
    target = _find_counter_var(inner.body)
    if target is None:
        return []
    N = _find_n_var(ctx.tree)
    return [_formula_text(target, N)]


def _is_dict_bruteforce_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if not isinstance(ctx.parent(node), ast.Module):
        return False
    if not (isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range'):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.For):
        return False
    inner = node.body[0]
    if not (isinstance(inner.iter, ast.Call) and isinstance(inner.iter.func, ast.Name) and inner.iter.func.id == 'range'):
        return False
    if not inner.body:
        return False
    first = inner.body[0]
    if not (isinstance(first, ast.Assign) and len(first.targets) == 1 and isinstance(first.targets[0], ast.Name)):
        return False
    val = first.value
    if not isinstance(val, ast.Call) or len(val.args) != 1:
        return False
    arg = val.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Mult)):
        return False
    names = set()
    if isinstance(arg.left, ast.Name):
        names.add(arg.left.id)
    if isinstance(arg.right, ast.Name):
        names.add(arg.right.id)
    loopvars = set()
    if isinstance(node.target, ast.Name):
        loopvars.add(node.target.id)
    if isinstance(inner.target, ast.Name):
        loopvars.add(inner.target.id)
    if not names or names != loopvars:
        return False
    return True


def _replace_dict_bruteforce_loop(node, ctx):
    tree = ctx.tree
    target = _find_final_print_var(tree) or 's'
    N = _find_n_var(tree)
    return [_formula_text(target, N)]


def _dict_keys_accum_target(for_node):
    it = for_node.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute) and it.func.attr == 'keys'):
        return None
    for sub in ast.walk(for_node):
        if isinstance(sub, ast.AugAssign) and isinstance(sub.target, ast.Name):
            return sub.target.id
        if isinstance(sub, ast.Assign) and len(sub.targets) == 1 and isinstance(sub.targets[0], ast.Name):
            v = sub.value
            if isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add):
                return sub.targets[0].id
    return None


def _is_dead_zero_init_for_dict_sum(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    if not (isinstance(node.value, ast.Constant) and node.value.value == 0):
        return False
    if not isinstance(ctx.parent(node), ast.Module):
        return False
    name = node.targets[0].id
    tree = ctx.tree
    after = False
    for stmt in tree.body:
        if stmt is node:
            after = True
            continue
        if not after:
            continue
        for sub in ast.walk(stmt):
            if isinstance(sub, ast.For):
                tgt = _dict_keys_accum_target(sub)
                if tgt == name:
                    return True
    return False


def _delete_statement(node, ctx):
    return [""]


def _is_dict_sum_final_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if not isinstance(ctx.parent(node), ast.Module):
        return False
    return _dict_keys_accum_target(node) is not None


def _is_strict_lt(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Lt))


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="trivial_digitroot_print_full_rewrite",
                match=_is_trivial_digitroot_print,
                replace=_replace_trivial_digitroot_print,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bruteforce_counter_loop_to_formula",
                match=_is_bruteforce_counter_loop,
                replace=_replace_bruteforce_counter_loop,
                symptoms=("timeout", "wrong"),
            ),
            Rewrite(
                name="bruteforce_dict_loop_to_formula",
                match=_is_dict_bruteforce_loop,
                replace=_replace_dict_bruteforce_loop,
                symptoms=("timeout", "wrong"),
            ),
            Rewrite(
                name="dead_zero_init_before_dict_sum_delete",
                match=_is_dead_zero_init_for_dict_sum,
                replace=_delete_statement,
                symptoms=("timeout", "wrong"),
            ),
            Rewrite(
                name="dict_sum_final_loop_delete",
                match=_is_dict_sum_final_loop,
                replace=_delete_statement,
                symptoms=("timeout", "wrong"),
            ),
            Rewrite(
                name="strict_lt_should_be_lte",
                match=_is_strict_lt,
                replace=_to_lte,
                symptoms=("wrong",),
            ),
        ]