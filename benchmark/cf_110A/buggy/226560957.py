num = input()
flag = True
for i in num:
    if i == "4" or i == "7":
        continue
    else:
        print("NO")
        flag = False
        break
if flag:
    print("YES")