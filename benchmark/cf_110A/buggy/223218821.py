n = list(input())
length = list(str(len(n)))
count = 0
res = 0
for i in n:
    if i == '4' or i == '7':
        res += 1
    else:
        break
if res == len(n):
    print('YES')
else:
    for i in length:
        if i == '4' or i == '7':
            count += 1
        else:
            break
    if len(length) == count:
        print("YES")
    else:
        print("NO")