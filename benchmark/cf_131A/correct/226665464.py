s = input()
if(s.upper()==s):
    print(s.lower())
else:
    s1=s[1:]
    s2=s1.upper()
    if s1==s2:
        print(s[0:1].upper()+s1.lower())
    else:
        print(s)