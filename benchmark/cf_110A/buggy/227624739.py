s = input()
k = 0
for e in s:
    if e == 4 or e == 7:
        k += 1
if k == 4 or k == 7:
    print("YES")
else:
    print("NO")