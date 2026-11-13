a = list(set(input()))
if "4" in a:
    a.remove("4")
if "7" in a:   
    a.remove("7")
if len(a) == 0:
    print("YES")
else:
    print("NO")