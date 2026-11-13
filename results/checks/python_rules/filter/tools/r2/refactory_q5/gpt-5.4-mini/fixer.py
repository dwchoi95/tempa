from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_topk_func(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "top_k"


def _is_return_slice_kplus1(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript)
            and isinstance(node.value.slice, ast.BinOp)
            and isinstance(node.value.slice.op, ast.Add)
            and isinstance(node.value.slice.right, ast.Constant)
            and node.value.slice.right.value == 1)


def _fix_return_slice_kplus1(node, ctx):
    return [ctx.text(node.value.value) + "[:k]"]


def _is_return_slice_constant_5(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript)
            and isinstance(node.value.slice, ast.Constant)
            and node.value.slice.value == 5)


def _fix_return_slice_constant_5(node, ctx):
    return [ctx.text(node.value.value) + "[:k]"]


def _is_return_wrong_var_after_sort(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript)
            and isinstance(node.value.value, ast.Name)
            and node.value.value.id in {"lst", "sort_list"} and isinstance(node.value.slice, ast.Name)
            and node.value.slice.id == "k")


def _fix_return_wrong_var_after_sort(node, ctx):
    return [ctx.text(node.value.value).replace(node.value.value.id, "sort") + "[:k]"]


def _is_append_max_remove_around(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "append")


def _fix_append_max_remove_around(node, ctx):
    return []


def _is_remove_then_append_max(node, ctx):
    if not isinstance(node, ast.While):
        return False
    body = node.body
    if len(body) < 2:
        return False
    return (isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Call)
            and isinstance(body[0].value.func, ast.Attribute)
            and body[0].value.func.attr == "remove"
            and isinstance(body[1], ast.Expr) and isinstance(body[1].value, ast.Call)
            and isinstance(body[1].value.func, ast.Attribute)
            and body[1].value.func.attr == "append")


def _fix_remove_then_append_max(node, ctx):
    return [ctx.text(node).replace("lst.remove(max(lst))\n        arranged.append(max(lst))",
                                  "arranged.append(max(lst))\n        lst.remove(max(lst))")]


def _is_zero_offbyone_while(node, ctx):
    return isinstance(node, ast.While) and isinstance(node.test, ast.Compare)


def _fix_zero_offbyone_while(node, ctx):
    txt = ctx.text(node.test)
    if "<=" in txt:
        return [ctx.text(node).replace(txt, txt.replace("<=", "<"))]
    return []


def _is_for_range_kminus1(node, ctx):
    return (isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
            and isinstance(node.iter.func, ast.Name) and node.iter.func.id == "range"
            and len(node.iter.args) == 1 and isinstance(node.iter.args[0], ast.BinOp)
            and isinstance(node.iter.args[0].op, ast.Sub)
            and isinstance(node.iter.args[0].right, ast.Constant)
            and node.iter.args[0].right.value == 1)


def _fix_for_range_kminus1(node, ctx):
    return [ctx.text(node).replace("-1", "")]


def _is_name_oldest(node, ctx):
    return isinstance(node, ast.Name) and node.id == "oldest"


def _fix_name_oldest(node, ctx):
    return ["biggest"]


def _is_name_ele(node, ctx):
    return isinstance(node, ast.Name) and node.id == "ele"


def _fix_name_ele(node, ctx):
    return ["element"]


def _is_append_pop_call(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "append" and len(node.args) == 1
            and isinstance(node.args[0], ast.Call)
            and isinstance(node.args[0].func, ast.Attribute)
            and node.args[0].func.attr == "remove")


def _fix_append_pop_call(node, ctx):
    return [ctx.text(node.args[0].args[0])]


def _is_k_zero_return_lst(node, ctx):
    return (isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
            and any(isinstance(op, ast.Eq) for op in node.test.ops)
            and any(isinstance(c, ast.Constant) and c.value == 0 for c in node.test.comparators)
            and len(node.body) == 1 and isinstance(node.body[0], ast.Return)
            and isinstance(node.body[0].value, ast.Name) and node.body[0].value.id == "lst")


def _fix_k_zero_return_lst(node, ctx):
    return [ctx.text(node).replace("return lst", "return []")]


def _is_append_max_without_remove(node, ctx):
    return (isinstance(node, ast.While) and any(isinstance(s, ast.Expr) for s in node.body)
            and "max(lst)" in ctx.text(node))


def _fix_append_max_without_remove(node, ctx):
    return []


def _is_return_sort_kplus1(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript)
            and isinstance(node.value.slice, ast.BinOp)
            and isinstance(node.value.slice.op, ast.Add)
            and isinstance(node.value.slice.right, ast.Constant)
            and node.value.slice.right.value == 1)


def _fix_return_sort_kplus1(node, ctx):
    return [ctx.text(node.value.value) + "[:k]"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_slice_k_plus_one", match=_is_return_slice_kplus1,
                    replace=_fix_return_slice_kplus1, symptoms=("wrong",)),
            Rewrite(name="return_slice_constant_five", match=_is_return_slice_constant_5,
                    replace=_fix_return_slice_constant_5, symptoms=("wrong",)),
            Rewrite(name="return_wrong_var_after_sort", match=_is_return_wrong_var_after_sort,
                    replace=_fix_return_wrong_var_after_sort, symptoms=("wrong",)),
            Rewrite(name="remove_then_append_max_swap", match=_is_remove_then_append_max,
                    replace=_fix_remove_then_append_max, symptoms=("wrong",)),
            Rewrite(name="while_off_by_one", match=_is_zero_offbyone_while,
                    replace=_fix_zero_offbyone_while, symptoms=("wrong",)),
            Rewrite(name="range_k_minus_one", match=_is_for_range_kminus1,
                    replace=_fix_for_range_kminus1, symptoms=("wrong",)),
            Rewrite(name="typo_oldest_to_biggest", match=_is_name_oldest,
                    replace=_fix_name_oldest, symptoms=("err:NameError", "wrong")),
            Rewrite(name="typo_ele_to_element", match=_is_name_ele,
                    replace=_fix_name_ele, symptoms=("err:NameError", "wrong")),
            Rewrite(name="append_remove_call_to_value", match=_is_append_pop_call,
                    replace=_fix_append_pop_call, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="k_zero_should_return_empty_list", match=_is_k_zero_return_lst,
                    replace=_fix_k_zero_return_lst, symptoms=("wrong",)),
            Rewrite(name="return_slice_k_plus_one_2", match=_is_return_sort_kplus1,
                    replace=_fix_return_sort_kplus1, symptoms=("wrong",)),
        ]