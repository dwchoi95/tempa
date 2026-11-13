from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

_COUNTER_WORDS = {"day", "days", "month", "months", "date", "dates"}


def _find_enclosing_function(node, ctx):
    n = node
    while True:
        n = ctx.parent(n)
        if n is None:
            return None
        if isinstance(n, ast.FunctionDef):
            return n


def _first_zero_init(func):
    for stmt in func.body:
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and isinstance(stmt.value, ast.Constant)
                and stmt.value.value == 0):
            return stmt.targets[0].id
    return None


def _canonical_counter_name(func):
    x = _first_zero_init(func)
    if x is None:
        return None
    param_name = func.args.args[0].arg if func.args.args else None
    if x == param_name:
        return x + "s"
    return x


# ---------------------------------------------------------------------------
# 1. comparator mistakenly refers to a counter-word instead of the parameter
# ---------------------------------------------------------------------------

def _is_miscompare_to_counter(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    if not isinstance(node.left, ast.Subscript):
        return False
    comparator = node.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    if comparator.id not in _COUNTER_WORDS:
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if not func.args.args:
        return False
    param_name = func.args.args[0].arg
    if comparator.id == param_name:
        return False
    return True


def _fix_miscompare(node, ctx):
    func = _find_enclosing_function(node, ctx)
    param_name = func.args.args[0].arg
    return [ctx.text(node.left) + " == " + param_name]


# ---------------------------------------------------------------------------
# 2. self increment `X = X + 1` using the wrong name for the counter
# ---------------------------------------------------------------------------

def _is_bad_self_increment(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    target = node.targets[0]
    val = node.value
    if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
        return False
    if not (isinstance(val.left, ast.Name) and val.left.id == target.id):
        return False
    if not (isinstance(val.right, ast.Constant) and val.right.value == 1):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    canon = _canonical_counter_name(func)
    if canon is None or canon == target.id:
        return False
    return True


def _fix_bad_self_increment(node, ctx):
    func = _find_enclosing_function(node, ctx)
    canon = _canonical_counter_name(func)
    return [canon + " = " + canon + " + 1"]


# ---------------------------------------------------------------------------
# 3. aug-increment `X += ...` using the wrong name for the counter
# ---------------------------------------------------------------------------

def _is_bad_self_augincrement(node, ctx):
    if not isinstance(node, ast.AugAssign):
        return False
    if not isinstance(node.target, ast.Name):
        return False
    if not isinstance(node.op, ast.Add):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    canon = _canonical_counter_name(func)
    if canon is None or canon == node.target.id:
        return False
    return True


def _fix_bad_self_augincrement(node, ctx):
    func = _find_enclosing_function(node, ctx)
    canon = _canonical_counter_name(func)
    return [canon + " += " + ctx.text(node.value)]


# ---------------------------------------------------------------------------
# 4. final check `X == 1` using the wrong name for the counter
# ---------------------------------------------------------------------------

def _is_bad_final_check(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    if not isinstance(node.left, ast.Name):
        return False
    if not (isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 1):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    canon = _canonical_counter_name(func)
    if canon is None or canon == node.left.id:
        return False
    return True


def _fix_bad_final_check(node, ctx):
    func = _find_enclosing_function(node, ctx)
    canon = _canonical_counter_name(func)
    return [canon + " == 1"]


# ---------------------------------------------------------------------------
# 5. the parameter gets shadowed by `param = 0` meant to be the counter
# ---------------------------------------------------------------------------

def _is_shadowing_counter_init(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    if not (isinstance(node.value, ast.Constant) and node.value.value == 0):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if not func.body or func.body[0] is not node:
        return False
    if not func.args.args:
        return False
    param_name = func.args.args[0].arg
    target = node.targets[0]
    return target.id == param_name


def _fix_shadowing_counter_init(node, ctx):
    target = node.targets[0]
    return [target.id + "s = 0"]


# ---------------------------------------------------------------------------
# 6. an accumulator declared as `()` later gets `.append(...)`ed (TypeError)
# ---------------------------------------------------------------------------

def _is_tuple_should_be_list(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    if not (isinstance(node.value, ast.Tuple) and len(node.value.elts) == 0):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None:
        return False
    name = node.targets[0].id
    for n in ast.walk(func):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == "append" and isinstance(n.func.value, ast.Name)
                and n.func.value.id == name):
            return True
    return False


def _fix_tuple_should_be_list(node, ctx):
    name = node.targets[0].id
    return [name + " = []"]


# ---------------------------------------------------------------------------
# 7. tuple accumulation forgets the trailing comma: `x = x + i` instead of
#    `x = x + (i,)`
# ---------------------------------------------------------------------------

def _is_tuple_concat_missing_comma(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    target = node.targets[0]
    val = node.value
    if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
        return False
    if not (isinstance(val.left, ast.Name) and val.left.id == target.id):
        return False
    right = val.right
    if not isinstance(right, ast.Name):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None:
        return False
    for stmt in ast.walk(func):
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and stmt.targets[0].id == target.id
                and isinstance(stmt.value, ast.Tuple)
                and len(stmt.value.elts) == 0):
            return True
    return False


def _fix_tuple_concat_missing_comma(node, ctx):
    target = node.targets[0]
    right_text = ctx.text(node.value.right)
    return [target.id + " = " + target.id + " + (" + right_text + ",)"]


# ---------------------------------------------------------------------------
# 8. trailing `if cond: return True` with no following fallback
# ---------------------------------------------------------------------------

def _is_dangling_if_return_true(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if node.orelse:
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not (isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is True):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month", "contains_unique_day"):
        return False
    if not func.body or func.body[-1] is not node:
        return False
    return True


def _fix_dangling_if_return_true(node, ctx):
    return [ctx.text(node) + "\nreturn False"]


# ---------------------------------------------------------------------------
# 9. the whole function body is a stub (`return` / `pass`)
# ---------------------------------------------------------------------------

def _stub_body_for(func_name, param1, param2):
    if func_name == "unique_day":
        return ("count = 0\n"
                 "for birthday in " + param2 + ":\n"
                 "    if birthday[1] == " + param1 + ":\n"
                 "        count += 1\n"
                 "return count == 1")
    if func_name == "unique_month":
        return ("count = 0\n"
                 "for birthday in " + param2 + ":\n"
                 "    if birthday[0] == " + param1 + ":\n"
                 "        count += 1\n"
                 "return count == 1")
    if func_name == "contains_unique_day":
        return ("for birthday in " + param2 + ":\n"
                 "    if birthday[0] == " + param1 + ":\n"
                 "        if unique_day(birthday[1], " + param2 + "):\n"
                 "            return True\n"
                 "return False")
    return None


def _is_stub_statement(node, ctx):
    if isinstance(node, ast.Return):
        if node.value is not None:
            return False
    elif isinstance(node, ast.Pass):
        pass
    else:
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month", "contains_unique_day"):
        return False
    if len(func.body) != 1 or func.body[0] is not node:
        return False
    if len(func.args.args) < 2:
        return False
    return True


def _fix_stub_statement(node, ctx):
    func = _find_enclosing_function(node, ctx)
    param1 = func.args.args[0].arg
    param2 = func.args.args[1].arg
    body = _stub_body_for(func.name, param1, param2)
    if body is None:
        return []
    return [body]


# ---------------------------------------------------------------------------
# 10. `if counter >= 2: return False` followed by bare `return True`
#     (fails to reject the zero-matches case)
# ---------------------------------------------------------------------------

def _is_counter_threshold_if(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if node.orelse:
        return False
    if len(node.body) != 1:
        return False
    ret = node.body[0]
    if not (isinstance(ret, ast.Return) and isinstance(ret.value, ast.Constant)
            and ret.value.value is False):
        return False
    test = node.test
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return False
    if not isinstance(test.left, ast.Name):
        return False
    if not isinstance(test.ops[0], (ast.GtE, ast.Gt)):
        return False
    if not (isinstance(test.comparators[0], ast.Constant)
            and isinstance(test.comparators[0].value, int)):
        return False
    parent = ctx.parent(node)
    body = getattr(parent, "body", None)
    if body is None or node not in body:
        return False
    idx = body.index(node)
    if idx + 1 >= len(body):
        return False
    nxt = body[idx + 1]
    if not (isinstance(nxt, ast.Return) and isinstance(nxt.value, ast.Constant)
            and nxt.value.value is True):
        return False
    return True


def _delete_counter_threshold_if(node, ctx):
    return [""]


def _is_trailing_return_true_after_threshold(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Constant)
            and node.value.value is True):
        return False
    parent = ctx.parent(node)
    body = getattr(parent, "body", None)
    if body is None or node not in body:
        return False
    idx = body.index(node)
    if idx == 0:
        return False
    prev = body[idx - 1]
    return _is_counter_threshold_if(prev, ctx)


def _fix_trailing_return_true(node, ctx):
    parent = ctx.parent(node)
    body = parent.body
    idx = body.index(node)
    if_node = body[idx - 1]
    counter_name = ctx.text(if_node.test.left)
    return ["return " + counter_name + " == 1"]


# ---------------------------------------------------------------------------
# 11. lowercase `true` / `false` typos
# ---------------------------------------------------------------------------

def _is_lowercase_true(node, ctx):
    return isinstance(node, ast.Name) and node.id == "true"


def _fix_lowercase_true(node, ctx):
    return ["True"]


def _is_lowercase_false(node, ctx):
    return isinstance(node, ast.Name) and node.id == "false"


def _fix_lowercase_false(node, ctx):
    return ["False"]


# ---------------------------------------------------------------------------
# 12. `counter <= 1` used where `counter == 1` is meant
# ---------------------------------------------------------------------------

def _is_counter_lte1(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.LtE):
        return False
    if not (isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 1):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    return True


def _fix_counter_lte1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


# ---------------------------------------------------------------------------
# 13. a stray `return counter` inside the counting for-loop short-circuits it
# ---------------------------------------------------------------------------

def _is_premature_loop_return(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    if not isinstance(node.value, ast.Name):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.For):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if len(parent.body) < 2:
        return False
    return True


def _fix_premature_loop_return(node, ctx):
    return [""]


# ---------------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="miscompare_counter_word_vs_param",
                    match=_is_miscompare_to_counter, replace=_fix_miscompare,
                    symptoms=("wrong",)),
            Rewrite(name="bad_self_increment_name",
                    match=_is_bad_self_increment, replace=_fix_bad_self_increment,
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="bad_self_augincrement_name",
                    match=_is_bad_self_augincrement, replace=_fix_bad_self_augincrement,
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="bad_final_check_name",
                    match=_is_bad_final_check, replace=_fix_bad_final_check,
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="param_shadowed_by_counter_init",
                    match=_is_shadowing_counter_init, replace=_fix_shadowing_counter_init,
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="tuple_accumulator_should_be_list",
                    match=_is_tuple_should_be_list, replace=_fix_tuple_should_be_list,
                    symptoms=("err:AttributeError",)),
            Rewrite(name="tuple_concat_missing_comma",
                    match=_is_tuple_concat_missing_comma, replace=_fix_tuple_concat_missing_comma,
                    symptoms=("wrong", "err:TypeError")),
            Rewrite(name="dangling_if_return_true_missing_else",
                    match=_is_dangling_if_return_true, replace=_fix_dangling_if_return_true,
                    symptoms=("wrong",)),
            Rewrite(name="stub_statement_fill_in",
                    match=_is_stub_statement, replace=_fix_stub_statement,
                    symptoms=("wrong", "err:TypeError")),
            Rewrite(name="delete_counter_threshold_guard",
                    match=_is_counter_threshold_if, replace=_delete_counter_threshold_if,
                    symptoms=("wrong",)),
            Rewrite(name="fix_trailing_return_true_after_threshold",
                    match=_is_trailing_return_true_after_threshold, replace=_fix_trailing_return_true,
                    symptoms=("wrong",)),
            Rewrite(name="lowercase_true_typo",
                    match=_is_lowercase_true, replace=_fix_lowercase_true,
                    symptoms=("err:NameError",)),
            Rewrite(name="lowercase_false_typo",
                    match=_is_lowercase_false, replace=_fix_lowercase_false,
                    symptoms=("err:NameError",)),
            Rewrite(name="counter_lte1_should_be_eq1",
                    match=_is_counter_lte1, replace=_fix_counter_lte1,
                    symptoms=("wrong",)),
            Rewrite(name="premature_loop_return",
                    match=_is_premature_loop_return, replace=_fix_premature_loop_return,
                    symptoms=("wrong",)),
        ]