from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_call_named(node, ctx, name):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name


def _is_digr_like(node, ctx):
    return isinstance(node, ast.FunctionDef) and any(
        isinstance(n, ast.Return) and isinstance(n.value, ast.Call)
        and isinstance(n.value.func, ast.Name) and n.value.func.id == node.name
        for n in ast.walk(node)
    )


def _replace_recursive_digital_root(node, ctx):
    func = node.name
    new_body = []
    for stmt in node.body:
        if isinstance(stmt, ast.Assign):
            txt = ctx.text(stmt)
            if "sum(int" in txt and "str(" in txt:
                txt = txt.replace("sum(int(dig) for dig in str(n))", "n if n < 10 else " + func + "(n)")
                txt = txt.replace("sum(int(d) for d in str(n))", "n if n < 10 else " + func + "(n)")
            new_body.append(txt)
        elif isinstance(stmt, ast.If):
            # Replace a recursive base-case style function body with iterative/correct root is too invasive.
            return []
        else:
            new_body.append(ctx.text(stmt))
    return new_body


def _is_print_of_input_call(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name) and node.value.func.id == "print"
            and len(node.value.args) == 1 and _is_call_named(node.value.args[0], ctx, "d"))


def _fix_print_input_to_int(node, ctx):
    arg = node.value.args[0]
    return [f"print(d(int({ctx.text(arg.args[0])})))"]


def _is_len_str_while(node, ctx):
    return isinstance(node, ast.While) and isinstance(node.test, ast.Compare) and len(node.test.ops) == 1 and isinstance(node.test.ops[0], ast.NotEq)


def _fix_len_str_while(node, ctx):
    test = node.test
    if isinstance(test.left, ast.Call) and isinstance(test.left.func, ast.Name) and test.left.func.id == "len":
        return [f"while {ctx.text(test.left.args[0])} >= 10:"]
    return []


def _is_range_i_to_n_plus_1(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"


def _fix_range_upper(node, ctx):
    if len(node.args) == 2 and isinstance(node.args[0], ast.Constant) and node.args[0].value == 1:
        b = ctx.text(node.args[1])
        if b.endswith("+1"):
            return [f"range(1, {b[:-2]})"]
    return []


def _is_wrong_root_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _fix_lt_to_le(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _is_double_loop_with_diagonal_bug(node, ctx):
    return isinstance(node, ast.For) and isinstance(node.target, ast.Name) and isinstance(node.iter, ast.Call)


class Fixer:
    def rules(self):
        return [
            Rewrite(name="print_input_needs_int_for_digital_root", match=_is_print_of_input_call,
                    replace=_fix_print_input_to_int, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="len_str_loop_should_use_nine_threshold", match=_is_len_str_while,
                    replace=_fix_len_str_while, symptoms=("wrong",)),
            Rewrite(name="range_upper_bound_off_by_one", match=_is_range_i_to_n_plus_1,
                    replace=_fix_range_upper, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_wrong_root_compare,
                    replace=_fix_lt_to_le, symptoms=("wrong",)),
        ]