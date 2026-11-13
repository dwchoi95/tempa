n=int(input())
f=3
c=0
b=0
while(n>=36):
    n=n-36
    c+=1
while(n>=3):
    n=n-3
    b+=1
if n==1:
    b+=0
    n=n-1
else:
    if n==2:
        b+=1
        n=n-2
print(c,b)