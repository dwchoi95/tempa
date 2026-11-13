def counter():
    n = 0
    def inc():
        nonlocal n
        n += 1
        return n
    return inc
c = counter(); c(); print(c())
g = 10
def setg():
    global g
    g = 20
setg(); print(g)
adders = [lambda x, k=k: x + k for k in range(3)]
print([a(10) for a in adders])
late = [lambda: k for k in range(3)]
print([f() for f in late])
def outer():
    x = "outer"
    class C:
        y = x
        def m(self): return x
    return C.y, C().m()
print(outer())
