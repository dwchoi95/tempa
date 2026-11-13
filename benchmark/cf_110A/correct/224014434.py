s = input()
n = 0
for i in range(len(s)):
    if int(s[i]) == 4 or int(s[i]) == 7:
        n = n+1
n = str(n)
v = 1
for i in range(len(n)):
    if int(n[i]) == 4 or int(n[i]) ==7:
        v = v*1
    else:
        v = 0
if v == 0:
    print('NO')
else:
    print('YES')