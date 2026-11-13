n = list(input())
l = 0
for i in n:
    if i == '4' or i == '7':
        l += 1

print('YES' if l == 4 or l == 7 else 'NO')