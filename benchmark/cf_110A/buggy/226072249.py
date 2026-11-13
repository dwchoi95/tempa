n = int(input())
n = str(n)
flag = 0
if "4" not in n or "7" not in n:
    flag =1
for x in n:
    if int(x) == 4 or int(x) == 7:
        continue
    else:
        flag =1
if flag:
    print("NO")
else:
    print("YES")