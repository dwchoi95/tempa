n = input()
length = list(str(len(n)))
count = 0
for i in length:
    if i == '4' or i == '7':
        count += 1
    else:
        break
if len(length) == count:
    print("YES")
else:
    print("NO")