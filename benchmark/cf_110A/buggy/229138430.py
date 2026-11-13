n = map(int,input())
a = [j for j in n]
a1 = len(a)
if a.count(4) + a.count(7) == a1:
    print('YES')
else:
    print('NO')