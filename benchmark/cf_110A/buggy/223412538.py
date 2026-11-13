a = int(input())
f = 1  # Initialize f to 1, assuming it's not a number composed of only 4s and 7s

while a > 0:
    c = a % 10

    if c == 4 or c == 7:
        f = 0
    else:
        f = 1
        break

    a = a // 10

if f == 0:
    print("yes")
else:
    print("no")