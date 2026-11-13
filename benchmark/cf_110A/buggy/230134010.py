n=input()
s=set()
for i in n:
    s.add(i)
if s=={'4','7'} or s=={'7','4'}:
    print("YES")
elif s=={'4'} or s=={'7'}:
    print("YES")

else:
    print("NO")