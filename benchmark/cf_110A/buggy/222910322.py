n=input()

t=set()
for i in n:
   t.add(i)
if('7' in t and '4' in t and len(t)==2):
   print("YES")
else:
    print("NO")