n = input()
x = n.count("7")
y = n.count("4")
z = x+y
print(x, y)
print(z)
print()
if x==0 and y==0:
    print("NO")
elif z==4 or z==7:
    print("YES")
else:
    print("NO")