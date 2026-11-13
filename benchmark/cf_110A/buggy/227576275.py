num = input()
output = "YES"
S = 0

for i in num:
    if i not in ["4","7"]:
        S += 1

if S != 4 or S != 7:
    output = "NO"


print(output)