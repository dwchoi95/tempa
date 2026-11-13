ch=input()
if ch[0]>="a" and ch[0]<="z":
    chup = ord(ch[0])
    chup = chup - 32
    chup = chr(chup)
    print(chup, end="")
else:
    print(ch[0],end="")


for i in range(1,len(ch)):
    if ch[i]>="A" and ch[i]<="Z":
       asci = ord(ch[i])
       asci = asci + 32
       asci = chr(asci)
       print(asci, end="")

    else:
        print(ch[i],end="")