n = input()

set_n = set(n)

total = 0

for i in list(set_n):
    if (i == "4") or (i == "7"):
        total = total
    else:
        total += 1
        
if total == 0:
    print("YES")
else:
    print("NO")