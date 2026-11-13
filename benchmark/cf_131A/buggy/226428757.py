n=input()
s=""
flag=False
for i in range(1,len(n)):
  if 65<=ord(n[i])<=90:
    flag=True
s+=n[0].upper()
if flag==True and 97<=ord(n[0])<=122:
  for i in range(1,len(n)):
    s+=n[i].lower()
  print(s)
else:
  print(n)