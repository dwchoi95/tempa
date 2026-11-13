x=int(input())
j=0
l=0
c=0
temp= 0
while j<x:
    l+=1
    j= j+l
    c+=1
    if j==x:
        break
if j>x:
    temp=j-x
    temp= int(temp/2)
    j= j-(2*temp)
    if j>x:
        c+=2
        
        
        
print(c)