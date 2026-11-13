def isLucky(n):
    x = n
    if (x == 0): return False
    while (x > 0):
        if not (x % 10 == 4 or x % 10 == 7):
            return False
        x = x // 10
    return True

n = input()
lds = sum((1 for x in n if x == '4' or x == '7'))
print("YES" if isLucky(lds) else "NO")