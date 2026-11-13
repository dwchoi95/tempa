counter = 0
num = input()

for i in num:
    if i == '4' or i == '7':
        counter += 1

    if counter == 4 or counter == 7:
        print("YES")
    else:
        print("NO")