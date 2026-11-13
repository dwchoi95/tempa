s=input()
n=len(s)
if s[0].islower() and s[1:].isupper():
    print(s[0].upper()+s[1:].lower())
else:
    c=0
    for i in s:
        if i.isupper():
            c+=1
    if c==n:
        print(s[0].upper()+s[1:].lower())
    else:
        print(s)