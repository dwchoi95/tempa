def f(a, b=2, *args, c, d=4, **kw):
    return (a, b, args, c, d, sorted(kw.items()))
print(f(1, c=3))
print(f(1, 5, 6, 7, c=8, e=9, d=0))
print(f(*[1, 2, 3], **{"c": 4, "z": 5}))
def g(x, /, y): return x - y
print(g(5, y=2))
for bad in [lambda: g(x=1, y=2), lambda: f(1), lambda: f(1, c=1, c2=2, **{"c": 3})]:
    try:
        bad()
    except TypeError:
        print("TypeError")
fs = []
for i in range(3):
    def h(x=i): return x
    fs.append(h)
print([h() for h in fs])
def acc(v, l=[]):
    l.append(v); return l
acc(1); print(acc(2))
