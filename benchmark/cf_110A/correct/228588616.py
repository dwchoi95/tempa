a=int(input())
c=str(a)
num=[]
for i in c:
  if i=='4':
    num.append(i)
  elif i=='7':
    num.append(i)
  else:
    pass


if len(num)==4 or len(num)==7:
  print("YES")
else: 
  print("NO")