n = int(input())
a = int(n / 36)
b = int(n % 36)
c = int(b / 3)

d = int(b % 3)

if d == 2:
    c = c + 1

print(str(a) + " " + str(c))