n = input()
valid = True
for i in n:
    if i != "4" and i != "7":
        valid = False
        break

if valid:
    print("YES")
else:
    print("NO")