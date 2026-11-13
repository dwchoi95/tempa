num = input()
output = "YES"
S = 0

for i in num:
    if i in ["4","7"]:
        S += 1

if S not in [4,7]:
    output = "NO"

print(output)