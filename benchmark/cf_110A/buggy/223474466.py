n = input()
nl = list(n)
a = []
b = []
for i in (nl):
    if i == "7" or i == "4" :
        a.append(i)
    else :
        b.append(i)
if len(b) == 0:
    print("YES")
else :
    print("NO")