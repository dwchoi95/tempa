n = input()
x = n.count("7")
y = n.count("4")
z = x+y
if x==0 and y==0:
    print("NO")
elif z%4==0 or z%7==0:
    print("YES")
else:
    print("NO")