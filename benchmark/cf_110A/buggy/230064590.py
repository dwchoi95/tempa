n = int(input())
k = 0
s = 0
s1 = 0
for i in str(n):
    if i == '4':
        k += 1
    elif i == '7':
        s += 1
    else:
        s1 += 1
if s1 == 0:
    m = 0
    for i in str(s + k):
        if i == '4' or i == '7':
            m += 1
    if m == len(str(s + k)):
        print('YES')
    else:
        print('NO')
else:
    print('NO')