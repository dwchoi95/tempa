from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _find_input_var(ctx):
    for node in ast.walk(ctx.tree):
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)):
            val = node.value
            if isinstance(val, ast.Call) and isinstance(val.func, ast.Name):
                if val.func.id == 'int' and len(val.args) == 1:
                    inner = val.args[0]
                    if (isinstance(inner, ast.Call)
                            and isinstance(inner.func, ast.Name)
                            and inner.func.id == 'input'):
                        return node.targets[0].id
                if val.func.id == 'input':
                    return node.targets[0].id
    return 'n'


def _self_increment_var(node):
    for sub in ast.walk(node):
        if (isinstance(sub, ast.AugAssign) and isinstance(sub.op, ast.Add)
                and isinstance(sub.target, ast.Name)):
            return sub.target.id
        if (isinstance(sub, ast.Assign) and len(sub.targets) == 1
                and isinstance(sub.targets[0], ast.Name)):
            name = sub.targets[0].id
            val = sub.value
            if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
                left_ok = isinstance(val.left, ast.Name) and val.left.id == name
                right_ok = isinstance(val.right, ast.Name) and val.right.id == name
                if left_ok or right_ok:
                    return name
    return None


def _formula_text(ivar):
    return (
        "_dr_q, _dr_r = divmod({iv}, 9)\n"
        "_dr_arr = [_dr_q] + [_dr_q+1]*_dr_r + [_dr_q]*(8-_dr_r)\n"
        "_dr_res = 0\n"
        "for _dr_i in range(9):\n"
        "    for _dr_j in range(9):\n"
        "        _dr_res += _dr_arr[_dr_i]*_dr_arr[_dr_j]*_dr_arr[(_dr_i*_dr_j)%9]\n"
        "for _dr_k in range(1, {iv}+1):\n"
        "    _dr_res -= {iv}//_dr_k"
    ).format(iv=ivar)


def _is_bruteforce_counter_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    parent = ctx.parent(node)
    if parent is None or not isinstance(parent, ast.Module):
        return False
    rvar = _self_increment_var(node)
    if rvar is None:
        return False
    return True


def _replace_bruteforce_counter_loop(node, ctx):
    ivar = _find_input_var(ctx)
    rvar = _self_increment_var(node)
    if rvar is None:
        return []
    text = _formula_text(ivar) + "\n{rv} = _dr_res".format(rv=rvar)
    return [text]


def _is_bogus_print_call(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    call = node.value
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            and call.func.id == 'print'):
        return False
    if len(call.args) != 1:
        return False
    inner = call.args[0]
    if not isinstance(inner, ast.Call):
        return False
    for a in inner.args:
        if isinstance(a, ast.Call) and isinstance(a.func, ast.Name) and a.func.id == 'input':
            return True
    return False


def _replace_bogus_print_call(node, ctx):
    text = "n = int(input())\n" + _formula_text('n') + "\nprint(_dr_res)"
    return [text]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="bruteforce_digital_root_counter_to_closed_form",
                match=_is_bruteforce_counter_loop,
                replace=_replace_bruteforce_counter_loop,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="missing_counting_logic_print_input_directly",
                match=_is_bogus_print_call,
                replace=_replace_bogus_print_call,
                symptoms=("wrong",),
            ),
        ]