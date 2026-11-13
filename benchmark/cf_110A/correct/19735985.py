from sys import stdin

n = stdin.readline().strip()

count = 0

for char in n:
    if char == '4' or char == '7':
        count += 1

for char in str(count):
    if char != '4' and char != '7':
        print('NO')
        exit()

print('YES')