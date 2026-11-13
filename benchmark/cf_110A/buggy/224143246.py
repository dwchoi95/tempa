l=input()
a=len(l)
a=str(a)
f=a.count('4')
h=a.count('7')
if f+h==len(a):
    print("YES")
else:
    print("NO")