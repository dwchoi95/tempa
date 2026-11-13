digit = input()
count = 0
count_4 = 0
count_7 = 0
flag = False
for ch in digit:
    if ch == '7' :
        count_7 += 1
    elif ch == '4':
        count_4 += 1
    else:
        flag = True
count = count_4 + count_7
if flag:
    if count_7 == 7 or count_7 == 4:
        print("YES")
    elif count_4 == 7 or count_4 == 4:
        print("YES")
    elif count == 4 or count == 7:
        print("YES")
    else:
        print("NO")
else:
    if count == 4 or count == 7:
        print("YES")
    else:
        print("NO")