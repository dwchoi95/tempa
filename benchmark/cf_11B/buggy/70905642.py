n=int(input())
i=0
a=0
s=0
while a!=n:
    if a+i+1>n:
        a=a-i-1
    else:
        a=a+i+1
    i=i+1
print(i)