a = int(input())
n = 0
for i in str(a):
    if i!="4" and i!="7":
        n+=1
if n==0:
    print("YES")
else:
    print("NO")