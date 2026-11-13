import math
import queue

from itertools import permutations 


n=int(input())

a=n//36

n%=36

b=n//3

if n%3==2:
    b+=1
    
print(a,b)