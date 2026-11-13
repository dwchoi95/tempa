import sys
n = input()
daudzums = 0
for i in n:
    daudzums = daudzums + 1

daudzums= str(daudzums)
print(daudzums)
f = 0
for k in daudzums:
    if daudzums[f] == "4" or daudzums[f] == "7":
        print("YES")
        sys.exit()
    f = f + 1
else:
    print("NO")