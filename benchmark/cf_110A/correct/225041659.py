skaitlis=str(input(""))
k=0
laimigie=0
while k<len(skaitlis):
    if skaitlis[k]=="4" or skaitlis[k]=="7":
        laimigie=laimigie+1
    k=k+1
if laimigie==4 or laimigie==7:
    print("YES")
else:
    print("NO")