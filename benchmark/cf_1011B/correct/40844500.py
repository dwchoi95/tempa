n,m=map(int,input().split())
a=list(map(int,input().split()))
b=[]
for i in set(a):
    b.append(a.count(i))
b.sort(reverse=True);r=0
for i in range(1,101):
    x=0
    for j in b:
        x+=j//i
        if x>=n:
            break
    if x>=n:
        r=max(r,i)
    else:break
print(r)