s=input()
i="ABCDEFGHIJKLMNOPQRSTUVWXYZ"
for a in range((len(s)-1),-1,-1):
    if s[a] not in i:
        if a==0:
            print(s[0].upper()+s[1:].lower())
        else:
            print(s)
            break
    else:
        if a==0:
            print(s.lower())
            break