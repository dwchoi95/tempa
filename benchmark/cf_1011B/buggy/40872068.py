import collections

n , m = map(int , input().split())

s = list(map(int , input().split()))
if n > m :
  print(0)
  exit()  
x = sorted(list(collections.Counter(s).values()))
if all(x) == 1:
  print(1)
  exit()
if x[0] == m : 
  print(m//3)
  exit()
if x[0] == 1:
  x.pop(0)
m = min(x)
z = 0
for j in x:
  z += j // m

if(z == n):
  print(m)
else :
  print(0)