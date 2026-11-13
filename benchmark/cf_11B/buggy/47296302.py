a = int(input())
n = 1
while True:
    if (n*n+n)/2 < a:
        n += 1
    elif (n*n+n)/2 == a:
        print(int(n))
        break
    elif (n*n+n)/2 > a:
        print(int(n+((n*n+n)/2-a)))
        break