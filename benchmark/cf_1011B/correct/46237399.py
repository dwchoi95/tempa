n,m=map(int,input().split())
food=list(map(int,input().split()))
count={}
for i in food:
  if(i in count.keys()):
    count[i]+=1
  else:
    count[i]=1
max_days=m//n
if(n>m):
  print(0);
else:
  flag=0
  for i in range(1,max_days+1):
    s=0
    for j in count:
      s+=count[j]//i
    if(s<n):
      flag=1
      break
  if(flag==1):
    print(i-1)
  else:
    print(i)