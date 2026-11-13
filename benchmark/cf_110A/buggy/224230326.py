n = input()
count_4 = 0
count_7 = 0
for i in n:
    if i == "4":
        count_4 += 1
    elif i == "7":
        count_7 += 1
    else:
        print("NO")
        quit()

if count_4 > 0 and count_7 > 0:
    print("YES")
else:
    print("NO")