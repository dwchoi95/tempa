def Check(days):
  global n,m,x
  pe=0
  for i in range(len(x)):
    pe+=x[i]//days
  if pe>=n: return True
  else: return False

n,m=map(int,input().split())
a=[*map(int,input().split())]
x=[]
b=dict()
for i in a:
  b[i]=b.get(i,0)+1
for i in b.values(): x.append(i)

left,right=0,100
while left<right:
  mid=(left+right+1)//2
  if Check(mid): left=mid
  else: right=mid-1
print(left)