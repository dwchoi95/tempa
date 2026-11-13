# O(n)

n = input()
contador = 0
for i in n:
    if i == '4' or i == '7':
        contador += 1
if contador == 7 or contador == 4:
    print("YES")
else:
    print("NO")