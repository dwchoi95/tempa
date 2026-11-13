s = input()
c = 0

for char in s:
    if char == '7' or char == '4':
        c += 1

if c == 7 or c == 4:
    print("YES")
else:
    print("NO")