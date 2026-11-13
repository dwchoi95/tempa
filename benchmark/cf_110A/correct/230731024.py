a=int(input(""))
a=str(a)
n=0
for i in a : 
  if i =='7' or i=='4':
    n=n+1

if n==4 or n==7 : 
  print("YES")
else :
  print("NO")