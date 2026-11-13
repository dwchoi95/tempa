x = input()
if len(x) == 0:
    print('NO')

sev, fou = 0, 0

for i in x:
    if i == '7':
        sev += 1
    elif i == '4':
        fou += 1

if sev+fou == len(x):
    print('YES')
else:
    print('NO')