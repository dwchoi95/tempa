import math
from math import sqrt
x=int(input())
if x<0:
    x=-x
ans=int(0)
r=int((-1+sqrt(1+4*x))/2)+1
for i in range(max(0,r-6),r+6,1):
    if i*(i+1)/2>=x:
        ans=i
        break
if (ans*(ans+1)//2-x)%2==1:
    ans=ans+1
if (ans*(ans+1)//2-x)%2==1:
    ans=ans+1
print(ans)