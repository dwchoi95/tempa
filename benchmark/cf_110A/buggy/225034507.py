def findlucky(n):
    while n > 0:
        d = n % 10
        if d != 4 and d != 7:
            return "NO"
        n //= 10
    return "YES"

n = int(input())
print(findlucky(n))