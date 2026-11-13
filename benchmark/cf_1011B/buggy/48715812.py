*a, = map(int, input().split()); *str, = map(int, input().split())
n, m, b = a[0], a[1], [0]*101
for i in range(m): b[str[i]]+=1
ans=0
for i in range(1,101):
    sum = 0
    for j in range(1,101):
        sum+=b[j]/i
    if sum>=n:ans=i
    if sum==0: breakb
print(ans)