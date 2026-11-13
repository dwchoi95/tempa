def isLucky(x):
    while (x >= 0):
        if not ((l:=x%10) == 4 or l == 7):
            return False
        x = x // 10
    return True

n = sum((1 for x in input() if x == '4' or x == '7'))
print("YES" if isLucky(n) else "NO")