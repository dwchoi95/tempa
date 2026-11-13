def fn(tot, L):
    l = len(L)
    if tot == 0:
        return -1
    elif l == 1:
        return l // tot
    else:
        ans = 0
        for i in range(1, tot + 1):
            if i > l:
                break
            z = fn(tot - i, L[1:])
            a1 = L[0] // i if z == -1 else min(L[0] // i, z)
            if a1 > ans:
                ans = a1
        return ans
            
[n, m] = [int(x) for x in input().split()]
A = [int(x) for x in input().split()]
if n > m:
    print("0")
else:
    di = {}
    for i in A:
        if i in di:
            di[i] += 1
        else:
            di[i] = 1
    L = []
    for i in di:
        L.append(di[i])
    L.sort(reverse = True)
    print(fn(n, L))