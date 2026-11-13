s = input()
t = 0
for i in range(len(s)):
    if s[i] == '4' or s[i] == '7':
        t += 1
t = str(t)
for i in range(len(t)):
    if t[i] == '4' or t[i] == '7':
        u = 0
    else:
        u = 1
        break
if u == 0:
    print('YES')
else:
    print('NO')