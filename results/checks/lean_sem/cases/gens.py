def g(n):
    for i in range(n):
        yield i
    return "done"
def h():
    r = yield from g(2)
    yield r
print(list(h()))
def s():
    yield 1
    raise StopIteration
try:
    list(s())
except RuntimeError as e:
    print("RuntimeError", type(e.__cause__).__name__)
it = g(1)
print(next(it), next(it, "dflt"))
def gg():
    x = yield
    yield x
q = gg(); next(q); print(next(q))
print(sum(i * i for i in g(4)), max(g(3)), sorted(g(3), reverse=True))
