a = int(input())
p = 0
i = 1
while p < a + 2 * i:
    p += i
    i += 1
    print(i)
    if p >= a and (p - i) % 2 == 0:
        if p == a:
            print(i - 1)
        else:
            print(i)
        break