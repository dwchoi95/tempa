import sys
n = input()
daudzums = 0
f= 0
for i in n:
    if n[f] == "4" or n[f] == "7":
        daudzums = daudzums + 1
if daudzums == 4 or daudzums == 7:
    print("YES")
else:
    print("NO")