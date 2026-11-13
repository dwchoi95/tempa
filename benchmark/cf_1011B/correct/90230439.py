n , m = map(int,input().split())
a = list(map(int,input().split()))
#a.sort()
d = {}

for i in range(m):
    if a[i] not in d :
        d[a[i]]  = 1
    else:
        d[a[i]] +=1

#print(d)

ans = 0
for i in range(1 , 101):
    p = 0
    for j in d.values():
        p += j // i

    if p >= n :
        ans = i

print(ans)