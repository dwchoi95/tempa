s=input()
a='qwertyuiopasdfghjklzxcvbnm'
b='QWERTYUIOPASDFGHJKLZXCVBNM'
q=0
e=0
w=0
if s[0] in a:
    for i in range(1,len(s)):
        if s[i] in b:
            q+=1
    if q==len(s)-1:
        print(s[0].upper()+s[1:].lower())
        w+=1
if s[0] in b:
    for j in range(1,len(s)):
        if s[j] in b:
            e+=1
    if e==len(s)-1:
        print(s[0].upper()+s[1:].lower())
        w+=1
if w==0:
    print(s)