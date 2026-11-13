for i in range(5):
    if i == 1: continue
    if i == 3: break
    print(i)
else:
    print("no")
for i in []:
    pass
else:
    print("else1")
n = 0
while n < 3:
    n += 1
else:
    print("else2", n)
while True:
    break
else:
    print("never")
def f(): raise StopIteration
d = {}
try:
    for d[f()] in [1]:
        pass
except StopIteration:
    print("target raised")
try:
    for x in [1, 2]:
        next(iter([]))
except StopIteration:
    print("body raised")
for a, b in [(1, 2), (3, 4)]:
    print(a + b, end=" ")
print()
for i in range(3):
    try:
        break
    except Undefined:
        pass
print("ok")
