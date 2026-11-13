cms=int(input())
from math import ceil 
inch=cms//36 
cms=cms%36 
al=cms%3 
if al==1 or al==0 :
    ans=cms//3 
else:
    ans=cms//3+1 
    
print(inch,ans)