x= int(input())
n=1
j=0
p= 0
while p<x:
    p= p+n
    j= j+1
    if p>x:
        p= p-2*n
    elif p==x:
        break
    n= n+1
    
print(j)