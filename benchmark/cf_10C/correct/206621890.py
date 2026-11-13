n = int(input())
q,r = divmod(n,9)
d = [q]+[q+1]*r+[q]*(8-r)
res = 0
for i in range(9):
    for j in range(9):
        res += d[i]*d[j]*d[(i*j)%9]
for i in range(1,n+1): res -= n//i
print(res)