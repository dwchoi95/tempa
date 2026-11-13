n = input()
count = 0
res = 0
for i in n:
    if i == '4' or i == '7':
        res += 1
if res == 4 or res == 7:
    print('YES')
else:
    print("NO")