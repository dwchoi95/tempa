n=int(input())
s1=str(n)
l=[i for i in s1]


c1=l.count('4')
c2=l.count('7')
c=c1+c2
c1=str(c)
l1=[i for i in c1]


if set(l)=={'4','7'}:
    print("YES!")
else:
    if c==4 or c==7 or set(l1)=={'4','7'}:
        print('YES')
    else:
        print("NO")