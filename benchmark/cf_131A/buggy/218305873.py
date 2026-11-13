s = input()
ucount = 0
for i in range(len(s)):
    if(s[i].isupper()):
        ucount += 1 
    if((ucount == len(s)-1) and (s[0].islower())):
        s = s.lower()
print(s.capitalize())