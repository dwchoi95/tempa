def lucky(x):
    a=list(x)
    b=[]
    flag=0
    while True:
       try:
        if x[flag]=="4" or x[flag]=="7":
            b.append(x[flag])
            flag+=1
        else:
            flag+=1
       except:
           break
    if "1" in list(str(len(b))) or "0" in list(str(len(b))) or "2" in list(str(len(b))) or "3" in list(str(len(b)))\
            or "5" in list(str(len(b))) or "6" in list(str(len(b))) or "8" in list(str(len(b))) \
            or "9" in list(str(len(b))):
        return False
    else:
        return True
print("YES" if lucky(input()) else "NO")