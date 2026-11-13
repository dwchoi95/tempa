n=int(input())
ch=str(n)
d=set(ch)
if len(d)==2 and (d =={'4','7'} or d =={'7','4'}):
    print("YES")
else:
    print("NO")