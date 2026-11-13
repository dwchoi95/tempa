a, b = input(), []

for i in range(len(a)):
    if a[i] in b:
        continue
    else:
        b += a[i]

if len(b) == 2 and '7' in b and '4' in b:
    print('YES')
else:
    print("NO")