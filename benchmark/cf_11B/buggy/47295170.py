x=int(input())
x=abs(x)
i,sum=0,0
while True:
    i+=1
    sum+=i
    if sum>=x:
        break
if sum==x:
    print(i)
elif sum>x:
    a=(sum-x)*2+i
    sum-=i
    b=i+(x-sum)*2-1
    if a>=b:
        print(b)
    elif a<b:
        print(a)