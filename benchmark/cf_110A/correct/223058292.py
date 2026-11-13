n=input()
t=0
for i in n:
    if int(i)==4 or int(i)==7:
        t+=1
    else:
        continue
if t==4 or t==7:
    print("YES")
else:
    print("NO")