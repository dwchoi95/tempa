x=int(input())
x=abs(x)
n=2
s=0
while s<x:
    s=(pow(n,2)-n)/2
    n=n+1
print(n-2)