res = 0

for i in input():
    if i not in "47":
        res = -1
        break
    res += 1

print("YES" if res in [4, 7] else "NO")