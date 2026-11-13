n,m = list(map(int, input().split()))
a = list(map(int,input().split()))
l = []
for i in range(101):
    l.append(0)
for i in range(m):
    l[a[i]] = l[a[i]] + 1
#l.sort(key = lambda x: x[1])
#print(l)
mx = 0
for j in range(1, 101):
    cp = list(l)
    poss = True
    for i in range(n):
        done = False
        for k in range(1, 101):
            if cp[k] >= j:
                cp[k] = cp[k] - j
                done = True
                break
        if not done:
            poss = False
            break
    if poss:
        mx = j
    else:
        break
print(mx)