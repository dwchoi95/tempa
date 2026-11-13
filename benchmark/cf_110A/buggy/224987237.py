s=input()
s=str(len(s))
l=["4", "7"]
f=0
for i in range(len(s)):
    if s[i] not in l:
        f=1
if f==1:
    print("NO")
else:
    print("YES")