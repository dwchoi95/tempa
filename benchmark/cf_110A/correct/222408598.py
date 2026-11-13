n = input()
counter = 0
for i in range(len(n)):
    if n[i] == '7' or n[i] == '4':
        counter += 1
counter = str(counter)
c = 0
for i in range(len(counter)):
    if counter[i] == '7' or counter[i] == '4':
        continue
    else:
        print('NO')
        c += 1
        break
if c == 0 : print('YES')