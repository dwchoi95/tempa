n = int(input())
n = str(n)

band = True
cont = 0
for i in n:
    if i not in "47":
        band = False
    else:
        cont += 1
        
print("YES") if band and (cont == 7 or cont == 4) else print("NO")