n=input()
a=[]
count=0
for i in n:
    a.append(i)
##print(a)

for j in a:
    if int(j)==4 or int(j)==7:
        count+=1
    else:
        continue
if count==4 or count==7:
    print("YES")
else:
    print("NO")