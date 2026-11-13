x = 1
a, (b, *c), d = 1, (2, 3, 4), 5
print(x, a, b, c, d)
p = q = [0]
q.append(1)
print(p)
del x
try:
    print(x)
except NameError:
    print("deleted")
def f():
    print(y)
    y = 2
try:
    f()
except UnboundLocalError:
    print("unbound")
i, j = j, i = 3, 4
print(i, j)
