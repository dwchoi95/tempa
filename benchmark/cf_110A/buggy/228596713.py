n = int(input())
L = []
nstr = str(n)
flag = True
for i in nstr:
    L.append(i)
    
for i in L:
    if i == "4" or i == "7":
        flag = True
    else:
        flag = False
        break

if flag == True:
    print("YES")
else:
    print("NO")