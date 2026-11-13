n = [int(i) for i in list(input())]

count = 0
for digit in n:
    if digit == 4 or digit == 7:
        count += 1

if count != 4 and count != 7:
    print("NO")
else:
    print("YES")