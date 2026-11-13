n=int(input())
s=str(n)
g=0
for ele in s:
    if ele not in "47":
        g=1
        print("No")
        break
    
if g==0:print("yes")