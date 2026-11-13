a=int(input())
b=0
c=str(a)
for i in range(len(c)):
    if c[i]=="4" or c[i]=="7":
        b+=1
if b==4 or b==7:
  print("YES")
else: 
  print("NO")