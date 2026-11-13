a=input()
count=0
m=0
for i in a:
   if i=='4' or i=='7':
      count+=1
for j in str(count):
   if j=='4' or j=='7':
      m+=1
   else:
      m-=10000000000000
if m>0:
   print('YES')
else:
   print('NO')