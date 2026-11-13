s = input()
ucount = 0
lcount = 0
for i in range(len(s)):
    if(s[i].isupper()):
        ucount += 1 
    else:
        lcount += 1
if((ucount == len(s)-1) and (s[0].islower())):
    for i in range(len(s)):
        if i == 0:
            print(s[i].upper(),end="")
        else:
            print(s[i].lower(),end="")
elif (ucount == len(s)):
    for i in range(len(s)):
        print(s[i].lower(),end="")
else:
    print(s)