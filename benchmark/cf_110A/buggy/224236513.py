n = input()
count = 0
for i in n:
    if i == "7" or i == "4":
        count += 1

if count == 7 or count == 4:
    print("YES")
else:
    for e in n:
        if e != "7" or e != "4":
            print("NO")
            quit()
if "4" in n and "7" in n:
    print("YES")