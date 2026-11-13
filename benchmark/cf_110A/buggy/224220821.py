n=int(input())
a=[]
c=0
while n/10!=0:
    s=n%10
    n=int(n/10)
    a.append(s)
for i in range(len(a)):
   if a[i] in [7,4]:
       c+=1
if c in [7,4]:
    print("YES")
else:
    print("NO")