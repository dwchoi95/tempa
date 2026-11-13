x,y=map(int,input().split())
a=set(map(int,input().split()))
ans=0
while len(a)!=0:
  x=list(a).pop()
  a.remove(x)
  if x%2==0:
    ans=ans+1
    x=x//2
    a.add(x)
print(ans)