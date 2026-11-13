# n,k=list(map(int,input().split()))
s=input()
f=False
for i in range(len(s)):
    if s[i] in "47":
        f=True
    else:
        f=False
        break
if f:
    print("YES")
else:
    print("NO")