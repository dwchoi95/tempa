a=input()
c1=0
c2=0
d=len(a)
if(d>1):
    for i in a:
        if i == "4":
            c1+=1
        if i == "7":
            c2+=1
    if((c1+c2)==4 or (c1+c2)==7):
        print("YES")
    else:
        print("NO")
else:
    print("NO")