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
        break
if count==len(a):
    print("YES")
else:
    print("NO")