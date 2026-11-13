n=input()
l=n.count('4')+n.count('7')

if l==4 or l==7 or l==len(n):
    print("YES")
else:
    print("NO")