a=int(input())
b=str(a)
counter=0
for i in b:
    if(i=="7"or i=="4"):
        counter=counter+1
if(counter==4 or counter==7):
    print("YES")
else:
    print("NO")