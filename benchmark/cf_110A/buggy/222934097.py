res = True

for i in input():
    if i != '4' and i != '7':
        res = False
        break

print("YES" if res else "NO")