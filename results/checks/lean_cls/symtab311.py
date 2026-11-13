"""Run under CPython 3.11, which keeps every comprehension as a nested function scope (3.12 and
later fold list, set, and dict comprehensions into the scope around them): read JSON-encoded
sources, one per line, and write for each its symbol tables as nested
[name, lineno, {symbol: local|free|global}, [children]], or null if 3.11 cannot parse it."""
import json
import symtable
import sys


def cls(t, s):
    if t.get_type() == "module":
        return "global"
    if s.is_declared_global() or s.is_global():
        return "global"
    if s.is_free() or getattr(s, "is_nonlocal", lambda: False)():
        return "free"
    if s.is_local() or s.is_parameter():
        return "local"
    return "global"


def dump(t):
    return [t.get_name(), t.get_lineno(), {s.get_name(): cls(t, s) for s in t.get_symbols()},
            [dump(c) for c in t.get_children()]]


for line in sys.stdin:
    try:
        out = dump(symtable.symtable(json.loads(line), "<p>", "exec"))
    except SyntaxError:
        out = None
    print(json.dumps(out))
