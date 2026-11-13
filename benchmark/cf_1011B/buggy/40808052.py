n,k = map(int,input().split(' '))

a = list(map(int,input().split(' ')))

z = [0]*(max(a)+1)

for i in range(k):
    z[a[i]]+=1

z = sorted(z)

s = n+1
i = 0
h = []
ans = -1
while s>n and i<len(z):
    if z[i]!=0:
        h = [x//z[i] for x in z]
        s = sum(h)
    i+=1

if z[i-1]<n:
    print(z[i-1])
else:
    print(n)