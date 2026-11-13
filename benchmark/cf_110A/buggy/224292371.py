s = input()
n = str(len(s))
t = 0
for i in range(len(n)):
    if n[i] != '4' and n[i] != '7':
        t = 1
        break
if t == 0:
    print('YES')
else:
    print('NO')