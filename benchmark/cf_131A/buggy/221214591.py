s=input()
k=s.upper()
if k==s:
    print(s)
else:
    print(k[0]+s[1:len(s)].lower())