a=str(input())
b=a.count("4")
c=a.count("7")
if ((b+c)-len(a))==0:
    print("YES")
else:
    print("NO")