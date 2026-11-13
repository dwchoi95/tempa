def findlucky(n):
    while n > 0:
        d = n % 10
        if d != 4 and d != 7:
            return "NO"
        n //= 10
    return "YES"

n = int(input())
if findlucky(n) == "YES":
    print("YES")
else:
    lucky = False
    for i in range(1, n+1):
        if n % i == 0 and findlucky(i) == "YES":
            lucky = True
            break
    if lucky:
        print("YES")
    else:
        print("NO")