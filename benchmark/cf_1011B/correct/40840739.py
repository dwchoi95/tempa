din = {}
def fn(tot, L, ind):
    if (tot, ind) in din:
        return din[(tot, ind)]
    l = len(L)
    if tot == 0:
        return -1
    elif ind == l - 1:
        return L[ind] // tot
    else:
        ans = 0
        for i in range(1, tot + 1):
            if i > L[ind]:
                break
            z = fn(tot - i, L, ind + 1)
            a1 = L[ind] // i if z == -1 else min(L[ind] // i, z)
            if a1 > ans:
                ans = a1
        din[(tot, ind)] = ans
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
    print(fn(n, L, 0))