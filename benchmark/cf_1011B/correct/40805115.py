n, k = input().strip().split(' ')
n, k = [int(n), int(k)]
a=list(map(int, input().strip().split(' ')))
list.sort(a)
from itertools import groupby
g=[len(list(group)) for key, group in groupby(a)]
#print(g)
mx=-1
list.sort(g)
for i in range(1,101):
     day=0
     #print(i)
     for j in range(len(g)):
          #print(g[j], i)
          day=day+int(g[j]/i)
          #print(day,'day')

     if (n<=day):
          mx=max(mx,i)
if mx>0:
     print(mx)
else:
     print('0')