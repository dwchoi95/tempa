"""Test values in JSON without losing their Python types.

A JSON round trip turns a tuple into a list, and `False == 0` in Python, so a
suite stored as plain JSON and compared with `==` accepts a program that
returns a list for a tuple or `False` for `0`. Tuples, sets, and dicts with
non-string keys are tagged instead, so `decode(encode(x))` has `x`'s type, and
the child compares outputs type-strictly.

Standard library only: the test child imports it from its own directory, and
`augment` inlines `SOURCE` into the generator child.
"""
from pathlib import Path

_TAGS = ("__tuple__", "__set__", "__dict__", "__repr__")


class Repr(str):
    """An output with no JSON form, kept as its repr."""


def encode(x):
    if x is None or isinstance(x, (bool, int, float, str)):
        return x
    if isinstance(x, list):
        return [encode(v) for v in x]
    if isinstance(x, tuple):
        return {"__tuple__": [encode(v) for v in x]}
    if isinstance(x, (set, frozenset)):
        return {"__set__": sorted((encode(v) for v in x), key=repr)}
    if isinstance(x, dict):
        if all(isinstance(k, str) for k in x) and not set(_TAGS) & x.keys():
            return {k: encode(v) for k, v in x.items()}
        return {"__dict__": [[encode(k), encode(v)] for k, v in x.items()]}
    return {"__repr__": repr(x)}


def decode(x):
    if isinstance(x, list):
        return [decode(v) for v in x]
    if isinstance(x, dict):
        if len(x) == 1 and next(iter(x)) in _TAGS:
            (k, v), = x.items()
            if k == "__tuple__":
                return tuple(decode(e) for e in v)
            if k == "__set__":
                return {decode(e) for e in v}
            if k == "__dict__":
                return {decode(a): decode(b) for a, b in v}
            return Repr(v)
        return {k: decode(v) for k, v in x.items()}
    return x


# everything above, for a child that cannot import this module
SOURCE = Path(__file__).read_text().split("\n# everything above")[0]


if __name__ == "__main__":
    for v in [(1, [2, (3,)]), {1: "a", (2, 3): {4}}, [True, 0, 1.5, None, "s"], {"k": ()}]:
        r = decode(encode(v))
        assert r == v and type(r) is type(v), (v, r)
    assert decode(encode((1,))) != [1] and type(decode(encode([1]))) is list
    print("ok")
