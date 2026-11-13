x= int(input())
n=1
j=0
p= 0
if x<0:
    x= x*(-1)
if x<11:
    while p<x:
        p= p+n
        j= j+1
        if p>x:
            p= p-2*n
        elif p==x and x<10:
            break
        n= n+1
else:
    while p<x:
        p= p+n
        j= j+1
        n=n+1
    if p>x:
        temp=p-x
        temp= int(temp/2)
        p= p-(2*temp)
        if p>x:
            j+=2

    
print(j)