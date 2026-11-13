n = int(input())
n = str(n)

band = True
for i in n:
    if i not in "47":
        band = False

print("YES") if band else print("NO")