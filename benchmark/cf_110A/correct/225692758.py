n = int(input())
i = 0
for d in str(n):
    if d == '4' or d == '7':
        i += 1
n = all(d == '4' or d == '7' for d in str(i))
if n:
    print("YES")
else:
    print("NO")