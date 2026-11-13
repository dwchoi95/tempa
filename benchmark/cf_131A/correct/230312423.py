s=input()
sub=s[1:]
if sub.upper()==sub:
    if ord(s[0])>=97:
        s=s[0].upper()+sub.lower()
    else:
        s=s.lower()
    print(s)
else:
    print(s)