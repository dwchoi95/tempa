t = 1
# t =  int(input())
while bool(t):
    n = int(input())
    lucky_digits = ['4', '7']
    cnt = 0

    for digit in str(n):
        if digit in lucky_digits:
            cnt += 1

    cnt = str(cnt)
    result = "YES" if cnt in lucky_digits else "NO"
    print(result)

    t -= 1