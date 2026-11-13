from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_num(node, value):
    return isinstance(node, ast.Constant) and node.value == value


def _is_str(node, value):
    return isinstance(node, ast.Constant) and node.value == value


def _is_lucky_digit_test(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (_is_num(node.comparators[0], 4) and ctx.text(node.left).strip() not in ("4", "'4'", '"4"'))
            or (_is_num(node.comparators[0], 7) and ctx.text(node.left).strip() not in ("7", "'7'", '"7"'))
            or (_is_num(node.left, 4) and ctx.text(node.comparators[0]).strip() not in ("4", "'4'", '"4"'))
            or (_is_num(node.left, 7) and ctx.text(node.comparators[0]).strip() not in ("7", "'7'", '"7"'))
        )
    )


def _fix_lucky_digit_test(node, ctx):
    if _is_num(node.comparators[0], 4):
        return [f"{ctx.text(node.left)} == '4'"]
    if _is_num(node.comparators[0], 7):
        return [f"{ctx.text(node.left)} == '7'"]
    if _is_num(node.left, 4):
        return [f"'4' == {ctx.text(node.comparators[0])}"]
    return [f"'7' == {ctx.text(node.comparators[0])}"]


def _is_input_string_count_double4(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.left, ast.Call)
        and isinstance(node.value.right, ast.Call)
        and isinstance(node.value.left.func, ast.Attribute)
        and isinstance(node.value.right.func, ast.Attribute)
        and node.value.left.func.attr == "count"
        and node.value.right.func.attr == "count"
        and len(node.value.left.args) == 1
        and len(node.value.right.args) == 1
        and _is_str(node.value.left.args[0], "4")
        and _is_str(node.value.right.args[0], "4")
    )


def _fix_input_string_count_double4(node, ctx):
    target = ctx.text(node.targets[0])
    expr = ctx.text(node.value)
    expr = expr.replace('.count("4") +', '.count("4") +').replace(".count('4') +", ".count('4') +")
    expr = expr.replace('.count("4")', '.count("7")', 1)
    expr = expr.replace(".count('4')", ".count('7')", 1)
    return [f"{target} = {expr}"]


def _is_wrong_mod_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (_is_num(node.comparators[0], 4) and "count" not in ctx.text(node.left))
            or (_is_num(node.comparators[0], 7) and "count" not in ctx.text(node.left))
        )
    )


def _fix_wrong_mod_check(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if _is_num(node.comparators[0], 4) or _is_num(node.comparators[0], 7):
        return [f"{left} == {right}"]
    return []


def _is_count_equals_len(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and any(isinstance(c, ast.Call) and isinstance(c.func, ast.Name) and c.func.id == "len" for c in node.comparators)
    )


def _fix_count_equals_len(node, ctx):
    txt = ctx.text(node)
    if "count ==" in txt or "len(" in txt:
        return [txt.replace("== len(", "== 4 or count == 7 and len(")]
    return []


def _is_count_incorrect_return(node, ctx):
    return isinstance(node, ast.Return) and "in (" in ctx.text(node.value) and "count" in ctx.text(node.value)


def _fix_count_incorrect_return(node, ctx):
    return ["return count in (4, 7)"]


def _is_sum_of_digits_wrong(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            "count('4')" in ctx.text(node.left) + ctx.text(node.comparators[0])
            or "count('7')" in ctx.text(node.left) + ctx.text(node.comparators[0])
        )
        and ("len(" in ctx.text(node.left) + ctx.text(node.comparators[0]))
    )


def _fix_sum_of_digits_wrong(node, ctx):
    return [ctx.text(node).replace("== len(t)", "== 4 or count_4 + count_7 == 7")]


def _is_for_range_off_by_one(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name)
        and node.iter.func.id == "range"
        and len(node.iter.args) == 2
        and isinstance(node.iter.args[1], ast.BinOp)
        and isinstance(node.iter.args[1].op, ast.Sub)
        and _is_num(node.iter.args[1].right, 1)
    )


def _fix_for_range_off_by_one(node, ctx):
    return [ctx.text(node.iter).replace("- 1", "")]


def _is_print_yes_no_case(node, ctx):
    return isinstance(node, ast.Constant) and isinstance(node.value, str) and node.value.lower() in {"yes", "no", "si", "yes!"}


def _fix_print_yes_no_case(node, ctx):
    v = node.value.upper()
    if v not in {"YES", "NO"}:
        return ["'YES'" if node.value.lower() in {"yes", "si", "yes!"} else "'NO'"]
    return [repr(v)]


def _is_print_input_noise(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "print" and len(node.value.args) == 1 and "input" not in ctx.text(node.value.args[0])


def _fix_print_input_noise(node, ctx):
    if "print(" in ctx.text(node):
        return [""]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="compare_digits_as_strings", match=_is_lucky_digit_test, replace=_fix_lucky_digit_test, symptoms=("wrong",)),
            Rewrite(name="double_count_of_four_should_be_four_and_seven", match=_is_input_string_count_double4, replace=_fix_input_string_count_double4, symptoms=("wrong",)),
            Rewrite(name="wrong_digit_comparison_fix", match=_is_wrong_mod_check, replace=_fix_wrong_mod_check, symptoms=("wrong",)),
            Rewrite(name="count_equals_length_should_be_count_in_47", match=_is_count_equals_len, replace=_fix_count_equals_len, symptoms=("wrong",)),
            Rewrite(name="return_count_in_47", match=_is_count_incorrect_return, replace=_fix_count_incorrect_return, symptoms=("wrong",)),
            Rewrite(name="off_by_one_range_end", match=_is_for_range_off_by_one, replace=_fix_for_range_off_by_one, symptoms=("wrong",)),
            Rewrite(name="normalize_yes_no_literals", match=_is_print_yes_no_case, replace=_fix_print_yes_no_case, symptoms=("wrong",)),
            Rewrite(name="remove_debug_print", match=_is_print_input_noise, replace=_fix_print_input_noise, symptoms=("wrong",)),
        ]