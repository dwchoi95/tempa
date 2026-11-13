n,m=map(int,input().split())
a=list(map(int,input().split()))
y=set (a)
y=list(y)
l=len(y)
t=[]
if (n>m ):
    exit(print("0"))
for i in y :
   t.append (a.count(i))
t.sort() 
#print(t)
ans=t[0]
sum=n+1
for i in range(l+1):
    print(sum,ans)
    if (sum>=n) :
       if (i==0):
         ans=t[0]
         #print("yes")
       else :
           ans=t[i-1]
           #print("no")
    else :
        exit (print(ans))
    sum=0
    for j in range(i,l):
     sum+=t[j]//t[i]