n=int(input())
n1=str(n)
count=0
for char in n1:
    if char=='4' or char=='7':
        count+=1
if count==7 or count==4:
    print("Yes")
else:
    print("NO")