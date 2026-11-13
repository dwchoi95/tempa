#print('hare krishna')
n,m=map(int,input().split())
l=[int(i) for i in input().split()]
lo=1 
hi=10**5 
ans=0 
from collections import Counter 
c=Counter(l)
#print(c)
def pzbl(mi):
    sm=0 
    for i in c:
        sm+=c[i]//mi 
    return sm>=n
while lo<=hi:
    mi=(lo+hi)//2
    if pzbl(mi):
        ans=mi 
        lo=mi+1 
    else:
        hi=mi-1 
print(ans)