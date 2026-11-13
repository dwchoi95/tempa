N = int(input())
c = 0

if N < 4:
    print("NO")
else:
    while N > 0:
        if (N % 10 == 4 or N % 10 == 7):
            c = c + 1
        N = N // 10

    is_lucky = True
    while c > 0:
        if (c % 10 != 4 and c % 10 != 7):
            is_lucky = False
            break
        c = c // 10

    if is_lucky:
        print("YES")
    else:
        print("NO")