x = input()
if x not in ['7', '4'] and (len(x) == 1):
    print('NO')
    exit()
elif x in ['4', '7'] and (len(x) == 1):
    print('YES')
    exit()

sev, fou = 0, 0
l = []
l[:] = x
for i in l:
    if i == '7':
        sev += 1
    elif i == '4':
        fou += 1
if sev+fou == len(x):
    print('YES')
else:
    print('NO')