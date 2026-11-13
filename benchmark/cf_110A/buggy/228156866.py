n=input("")

s=n.count('7')
f=n.count('4')
q=str(len(n))
s2=q.count('7')
f2=q.count('4')
if len(n)==(s+f) and len(q)==(s2+f2):
    print("YES")
  
else:
  print("NO")