w=int(input("enter"))
while w!=0:
    if w%10==4:
        w=w//10
    elif w%10==7:
        w=w//10
    else:
        print("NO")
        break
x=str(w)
if len(x)==4 and 7:
    print("YES")