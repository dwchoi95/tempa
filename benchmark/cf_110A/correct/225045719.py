n=str(input())
cik=n.count("4")
cik2=n.count("7")

cik3=cik+cik2
if (cik3==7):
    print("YES")
elif (cik3==4):
    print("YES")
else:
    print("NO")