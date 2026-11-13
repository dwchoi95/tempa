n=(input())
#a=int(n)
sum=0
for i in n:
    if i=="4" or i=="7":
        sum=sum+1
print(sum)
sumi=0
b=str(sum)
for i in b:
    if i=="4" or i== "7":
        sumi=sumi+1
if sumi==len(b):
    print("YES")
else:
    print("NO")