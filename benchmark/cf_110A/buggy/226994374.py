n=int(input())
f=str(n)
l=list(f)
s=set(l)

c1=l.count('4')
c2=l.count('7')
a=['1','2','3','5','6','8','9','0']

if s=={'4','7'}:
    print("YES")
else:
    if c1==4 or c1==7 or c2==4 or c2==7:
        print("YES")
    else:
        print("NO")