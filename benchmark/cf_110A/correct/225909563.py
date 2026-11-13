num = input()
i = 0

for digit in num :
    if digit == "4" or digit == "7" :
        i += 1

z = 0

for digit in str(i) :
    if digit == "4" or digit == "7" :
        z += 1

if z == len(str(i)) :
    print("YES")
else :
    print("NO")