n = input()
b = list(map(int,list(n)))
count = 0
for i in range(len(b)):
    if b[i] == 4 or b[i] == 7:
        count += 1
if (count % 4 == 0 or count % 7 == 0) and count != 0:
    print('YES')
else: print('NO')