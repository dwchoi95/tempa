digit = input()
count = 0
flag = False
for ch in digit:
    if ch == '7' or ch == '4':
        count += 1
    else:
        flag = True
if flag:
    if count == 7 or count == 4:
        print("YES")
    else:
        print("NO")
else:
    print("YES")