n=int(input())
f=n//36
r=n%36
if r%3==0:
    i=r//3
elif r%3==1:
    i=r//3
elif r%3==2:
    i=r//3+1
print(f,i)