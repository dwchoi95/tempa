def Solve(n):
    a=-1
    b=1000000000
    while(b-a>1):
        e=(b+a)//2
        x=(e*(e+1))//2
        if(x>=n):
            b=e
        else:
            a=e
    x=(b*(b+1))//2
    if((x-n)%2==0):
        return b
    return b+1


x=int(input())
x=abs(x)
print(Solve(x))