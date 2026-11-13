n=input()
s=list(n)
f=s.count('4')
si=s.count('6')
if f+si==4 or f+si==7:
    print("YES")
else:
    print("NO")