n=int(input())
s=str(n)
g=0
for ele in s:
    if ele in "47":
        g+=1
        
if g==len(s):print("YES")
else:print("NO")