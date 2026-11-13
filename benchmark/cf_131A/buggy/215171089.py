ch=input()
chup = ord(ch[0])
chup = chup-32
chup = chr(chup)
print(chup, end="")

for i in range(1,len(ch)):
    if ch[i]>="A" and ch[i]<="Z":
       asci = ord(ch[i])
       asci = asci + 32
       asci = chr(asci)
       print(asci, end="")

    else:
        print(ch[i])