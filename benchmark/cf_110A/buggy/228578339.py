n=int(input(""))
ch=str(n)
i=0
test=True
while i<len(ch) and test:
    if ch[i]!="7" and ch[i]!="4":
        test=False
    else:
        i+=1
if test:
    print("YES")
else:
    print("NO")