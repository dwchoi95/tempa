n = input()

l = len(n)

c = True
for _ in range(len(str(l))):
    if l%10 == 4 or l % 10 == 7:
        l = l//10
    else:
        c = False
        break

if c:
    print('YES')

else:
    print('NO')