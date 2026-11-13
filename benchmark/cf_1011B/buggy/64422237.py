n,m=map(int,input().split())
l=list(map(int,input().split()))
c=m//n
h=[]
y=0
k=0
if n>m:
    print(0)
else:
    for i in l:
        if i not in h and l.count(i)>=c :
            h.append(i)
            y=y+(l.count(i)//c)
        if y<c:
            c=c-1
    print(c)