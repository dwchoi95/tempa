n=int(input())
m=abs(n)
i=0
while m-i>=0:
    m=m-i
    i=i+1
if m==0:
    print(i-1)
else:
    if m<=(i//2):
        print(i-1+2*m)
    else:
        print(i+2*(i-m))