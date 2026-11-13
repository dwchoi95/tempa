n, k=map(int, input().split()); s={}
a=list(map(int, input().split())); d=102*[0]; b=0;
for t in range(k):
    d[a[t]]+=1
    s[a[t]]=d[a[t]]
s=list(s.values())
s.sort()
s.reverse()
m=max(s)
for t in range(m):
    x=m-t
    l=m//x
    p=l
    for i in s[1:]:
        p+=i//x
    if p>=n:
        b=1
        print (x)
        break
if b==0:
    print(0)