n=int(input())
a=n//3
b=n%3
if b==2:
    a=a+1
p=a//12
q=a%12
print(p,q)