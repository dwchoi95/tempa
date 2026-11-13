n = input()

total = 0

for i in list(n):
    if i == "4" or i == "7":
        total += 1
        
    else:
        total = total
        
if total == 4 or total == 7:
    print("YES")
else:
    print("NO")