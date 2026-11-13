s=input()
k=0
l=["4", "7"]
f=0
for i in range(len(s)):
    if s[i] in l:
        k+=1
k=str(k)
for j in range(len(k)):
    if k[j] not in l:
        f=1
if f==1:
    print("NO")
else:
    print("YES")