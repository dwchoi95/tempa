n,m=map(int,input().split())
l=list(map(int,input().split()))
z={}
for i in l:
  if(i in z):
    z[i]=z[i]+1
  else:
    z[i]=1
l=list(z.values())
l.sort(reverse=True)
for i in range(len(l)):
  if(i>n):
    l.pop()
ans=[]
f=[]
noans=0
for i in range(len(l)):
  ans.append(1)
  f.append(0)
while(n>0):
  maxi=0
  for i in range(1,len(l)):
    if(l[i]//ans[i]>l[maxi]//ans[maxi]):
      maxi=i
  ans[maxi]=ans[maxi]+1
  if(l[maxi]//ans[maxi]==0 and f[maxi]==1):
    noans=1
    break
  f[maxi]=1
  n=n-1
mini=0
for i in range(len(l)):
  if(f[i]==1):
    if(l[mini]/(ans[mini]-1)>l[i]//(ans[i]-1)):
      mini=i
  else:
    break
if(noans):
  print(0)
else:
  print(l[mini]//(ans[mini]-1))