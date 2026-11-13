n =input()
n = [int(i) for i in n]
n1 =n.count(4) + n.count(7)
if n1==7 or n1==4:
    print("YES")
else:
    print("NO")