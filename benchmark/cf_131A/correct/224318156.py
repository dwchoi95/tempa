h=input()

if h.isupper():
    print(h.lower())
else:
    u=0
    for i in range(0,len(h),1):
        if h[i].isupper():
            u+=1
    if u==len(h)-1 and h[0].islower():
        y=""
        y+=h[0].upper()
        y+=h[1:].lower()
        print(y)
    else:
        print(h)
#