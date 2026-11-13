n=int(input())
c=0
s=str(n)
a=s.count('4')
b=s.count('7')
c=a+b
d=int(c)
if(d==4 or d==7):
    print("YES")
else:
    print("NO")