n=int(input())
p=n
g=0
d=0
while p>0:
    x=p%10
    p=p//10
    d=d+1
    if(x==4 or x==7):
        g=g+1
if d==g:
    print("YES")
else :
    y=g
    q=0
    e=0
    while y>0:
        x=y%10
        y=y//10
        q=q+1
        if x==4 or x==7 :
            e=e+1
    if q==e:
        print("YES")
    else:
        print("NO")