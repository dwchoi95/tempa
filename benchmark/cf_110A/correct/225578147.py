a,n,k=str(input()),0,0
for i in a:
    if i=="4" or i=="7":
        n+=1
for j in str(n):
    if j=="4" or j=="7":
        k+=1
if len(str(n))==k:
    print("YES")
else:
    print("NO")