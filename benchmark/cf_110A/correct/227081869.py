s = input()
n = 0
for i in range(len(s)):
    if s[i] == '4' or s[i] == '7':
        n += 1
    else:
        continue
if n == 4 or n == 7:
    print('YES')
else:
    print('NO')