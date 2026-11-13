ch=input("")
if "a"<=ch[0]<="z":
    ch1=chr(ord(ch[0])-32)
else:
    ch1=ch[0]
for i in range(1,len(ch)):
    if "A"<=ch[i]<="Z":
        ch1=ch1+chr(ord(ch[i])+32)
    else:
        ch1=ch1+ch[i]
print(ch1)