def t(v): print("t", v); return v
def deco(n):
    print("deco", n)
    def d(f):
        print("apply", n)
        return f
    return d
@deco(1)
@deco(2)
def f(a=t("default")): return a
print(f())
def twice(fn):
    def w(*a): return fn(*fn(*a))
    return w
@twice
def sw(x, y): return y, x
print(sw(1, 2))
from functools import lru_cache
@lru_cache(maxsize=None)
def fib(n): return n if n < 2 else fib(n - 1) + fib(n - 2)
print(fib(60))
