number=input()
n="12356089"

for x in number:
    if x in n or number=="7":
        print("NO")
        exit()
print("YES")