a = int(input())
n = 1
while True:
    if a == 0:
        print(0)
        break
    elif a > 0:
        if (n*n+n)/2 < a:
            n += 1
        elif (n*n+n)/2 == a:
            print(int(n))
            break
        elif (n*n+n)/2 > a:
            c = int(n+(((n*n+n)/2)-a)*2)
            d = int(n-1+(a-(n*(n-1))/2)*2)
            print(min(c, d))
            break
    elif a<0:
        a = abs(a)
        if (n*n+n)/2 < a:
            n += 1
        elif (n*n+n)/2 == a:
            print(int(n))
            break
        elif (n*n+n)/2 > a:
            c = int(n+(((n*n+n)/2)-a)*2)
            d = int(n-1+(a-(n*(n-1))/2)*2)
            print(min(c, d))
            break