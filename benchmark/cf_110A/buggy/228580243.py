a = list(set(input()))
if "4" in a:
    a.remove("4")
if "7" in a:   
    a.remove("7")
print("NO" if len(a)!=0 else "Yes")