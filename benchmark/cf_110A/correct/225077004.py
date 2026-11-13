n = input()
s = 0
for i in range(0, len(n)):
    if n[i] == '4' or n[i] == '7':
        s = s+1
if s == 4 or s == 7:
    print('YES')
else:
    print('NO')