s=int(input(""))
x=str(s)  
count=0
for i in range(len(x)):
    if int(x[i])==4 or int(x[i])==7:
        count+=1
    else:
        pass
if count==4 or count==7:
    print("YES")
else:
    print("NO")