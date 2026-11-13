from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_int(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _match_plus2_div3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.left, ast.Call)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
        and _is_input_int(node.left.left)
    )


def _replace_plus2_div3(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_div3_plus2(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
    )


def _replace_div3_plus2(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_round_half_up(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 3
    )


def _replace_round_half_up(node, ctx):
    x = ctx.text(node.args[0].left)
    return [f"{x} // 3 + (1 if {x} % 3 == 2 else 0)"]


def _match_float_round_div36(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 36
    )


def _replace_float_round_div36(node, ctx):
    return [f"({ctx.text(node.args[0].left)} + 1) // 36"]


def _match_div36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_div36(node, ctx):
    return [f"({ctx.text(node.left)} + 1) // 36"]


def _match_mod36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_mod36(node, ctx):
    return [f"({ctx.text(node.left)} + 1) % 36"]


def _match_round_div3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 3
    )


def _replace_round_div3(node, ctx):
    return [f"({ctx.text(node.args[0].left)} + 1) // 3"]


def _match_canon_round_div3(node, ctx):
    return _match_round_div3(node, ctx)


def _replace_canon_round_div3(node, ctx):
    return [f"({ctx.text(node.args[0].left)} + 1) // 3"]


def _match_cmp_ge_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_cmp_ge_2(node, ctx):
    return [f"{ctx.text(node.left)} == 2"]


def _match_cmp_eq_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_cmp_eq_1(node, ctx):
    return [f"{ctx.text(node.left)} <= 1"]


def _match_inch_to_feet_mod(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 12
    )


def _replace_inch_to_feet_mod(node, ctx):
    return [f"({ctx.text(node.left)}) % 12"]


def _match_bad_print_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print" and any(
        isinstance(a, ast.Constant) and isinstance(a.value, str) and "  " in a.value for a in node.args
    )


def _replace_bad_print_call(node, ctx):
    args = [ctx.text(a) for a in node.args]
    return [f"print({', '.join(args)})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="add_one_before_div3", match=_match_plus2_div3, replace=_replace_plus2_div3, symptoms=("wrong",)),
            Rewrite(name="add_one_before_div3_commuted", match=_match_div3_plus2, replace=_replace_div3_plus2, symptoms=("wrong",)),
            Rewrite(name="round_cm_to_inches_half_up", match=_match_round_half_up, replace=_replace_round_half_up, symptoms=("wrong",)),
            Rewrite(name="float_int_div36_to_round_div36", match=_match_float_round_div36, replace=_replace_float_round_div36, symptoms=("wrong",)),
            Rewrite(name="floor_div36_off_by_one", match=_match_div36, replace=_replace_div36, symptoms=("wrong",)),
            Rewrite(name="mod36_off_by_one", match=_match_mod36, replace=_replace_mod36, symptoms=("wrong",)),
            Rewrite(name="round_div3_to_integer_formula", match=_match_round_div3, replace=_replace_round_div3, symptoms=("wrong",)),
            Rewrite(name="ge_two_should_eq_two", match=_match_cmp_ge_2, replace=_replace_cmp_ge_2, symptoms=("wrong",)),
            Rewrite(name="eq_one_should_lte_one", match=_match_cmp_eq_1, replace=_replace_cmp_eq_1, symptoms=("wrong",)),
            Rewrite(name="mod_twelve_result", match=_match_inch_to_feet_mod, replace=_replace_inch_to_feet_mod, symptoms=("wrong",)),
            Rewrite(name="normalize_print_spacing", match=_match_bad_print_call, replace=_replace_bad_print_call, symptoms=("wrong",)),
        ]