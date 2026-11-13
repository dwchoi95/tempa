n=input()
l=n.count('4')+n.count('7')

if l==4 or l==7 or all(d in['4','7'] for d in n):
    print("YES")
else:
    print("NO")