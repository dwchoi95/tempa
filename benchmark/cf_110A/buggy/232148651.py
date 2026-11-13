a = int(input())
b = str(a)
count = len(b)
flag = 0

for i in b:
    if i not in {'4', '7'}:
        flag = 1
        break
    else:
        flag = 0

if flag == 0 and (count == 4 or count == 7):
    print("YES")
else:
    print("NO")