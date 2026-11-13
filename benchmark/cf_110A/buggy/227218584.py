entrada = list(input())
print(entrada)
luckyNumber = 0
for i in entrada:
    if i=="4" or i=="7":
        luckyNumber += 1

if luckyNumber == 4 or luckyNumber == 7:
    print("YES")
else:
    print("NO")
print(luckyNumber)