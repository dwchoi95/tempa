a=input()
b=a.count("4")
b+=a.count("7")
for i in str(b):
    if i in ["4","7"]:
        print("YES")
    else:
        print("NO")