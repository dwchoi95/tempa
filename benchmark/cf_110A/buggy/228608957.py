n = list(input())
total =n.count("4")+n.count("7")
a = list(set(n))
if "4" in a:
    if "7" in a:   
        a.remove("4")
        a.remove("7")
if total==7or total==4 or len(a) == 0  :
    print("YES")
else:
    print("NO")