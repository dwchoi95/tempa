x = input()
l = []
l[:] = x
n = 0

if len(x) == 0 or len(x) == 1 and x != '7' or len(x) == 1 and x != '4':
    print('NO')
    exit()
elif len(x) == 1 and x == '7' or len(x) == 1 and x == '4':
    print('YES')
    exit()

for i in range(len(l)-1):
    if l[i] in ['7', '4'] and l[i+1] in ['7', '4']:
        n += 1
if n > 0:
    print('YES')
    exit()
print('NO')