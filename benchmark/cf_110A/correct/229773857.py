#nearly lucky number
n = int(input())
s = str(n)
c = []
for i in range(len(s)):
    if s[i]=='4':
       c.append(1)
    elif s[i]=='7':
       c.append(1)
x = sum(c)
if x== 7 or x==4:
   print('YES')
else : 
   print('NO')