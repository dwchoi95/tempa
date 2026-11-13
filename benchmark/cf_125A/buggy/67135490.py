n=int(input())
a=int(n/36)
b=n%36
if b%3==0 or b%3==1:
    b=int(b/3)
else:
    b=int(b/3)+1
print(a,b)