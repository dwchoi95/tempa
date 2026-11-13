n=int(input())
x1=n//36
x2=n%36
a=x1
b1=x2//3
b2=x2%3
if b2==1 or b2==0:
    b=b1
else:
    b=b1+1
print(a,b,end=" ")