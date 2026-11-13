def digr(n):
    x = sum(int(dig) for dig in str(n))
    if x<10:
        return x
    else:
        return digr(x)
n=int(input())
d=0
for i in range(1,n+1):
    for j in range(i,n+1):
        c=digr(digr(i)*digr(j))
        if c<n+1 and c!=i*j:
            d=d+2
print(d)