print([x * y for x in range(3) if x for y in range(x)])
print({x % 3 for x in range(10)}, {k: v for k, v in zip("abc", range(3))})
g = (x * 2 for x in range(4))
print(next(g), list(g), sum(x for x in range(5)))
print([(n := n + 1) for _ in range(3)] if (n := 0) == 0 else None, n)
class K:
    v = 5
    w = [i for i in range(v)]
print(K.w)
try:
    class L:
        v = 5
        w = [v + i for i in range(2)]
except NameError:
    print("NameError")
def f():
    try:
        print([x for _ in [1]])
    except UnboundLocalError:
        print("UnboundLocalError")
    try:
        print(list(x for _ in [1]))
    except NameError as e:
        print(type(e).__name__)
    x = 1
f()
print([[i * j for j in range(3)] for i in range(2)], sorted({(a, b) for a in "ab" for b in "c"}), {(i, -i) for i in range(4)})
