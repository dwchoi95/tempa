n=int(input())
a=n//36
c=(n%36)
if c%3==2:
    b=(c//3)+1
else:
    b=c//3
print(a,b)