n, m = map(int, input().split())
a = [int(i) for i in input().split()]
if m >= n:
    b = []
    for item in set(a):
        b.append(a.count(item))
    if len(b) == 1:
        print(b[0] // n)
    else:
        while len(b) < n:
            b.sort()
            b.append(b[-1] // 2)
            b[-2] = b[-2] // 2 + b[-2] % 2
        b.sort()
        while b[-1] // 2 > b[0]:
            b[0] = b[-1] // 2
            b[-1] = b[-1] // 2 + b[-1] % 2
            b.sort()
        print(b[0])
else:
    print(0)