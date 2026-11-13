n = input()
N = 0
for i in range(len(n)):
    if n[i] == '4' or n[i] == '7':
        N += 1
if N == 0:
    print('NO')
else:
    L = []
    for i in range(len(str(N))):
        L.append([])
    L[0].append(4)
    L[0].append(7)
    for i in range(1,len(str(N))):
        for j in range(len(L[i-1])):
            L[i].append(L[i-1][j]*10+4)
            L[i].append(L[i-1][j]*10+7)
    a = 0
    for i in range(len(str(N))):
        for j in range(len(L[i])):
            if N == L[i][j]:
                print('YES')
                a += 1
    if a == 0:
        print('NO')