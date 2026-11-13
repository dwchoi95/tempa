n = int(input())
L = []
nstr = str(n)
flagg = True
for i in nstr:
    L.append(i)
    
for i in L:
    if i == "4" or i == "7":
        flagg = True
    else:
        flagg = False
        break

if flagg == True:
    print("YES")
else:
    print("NO")