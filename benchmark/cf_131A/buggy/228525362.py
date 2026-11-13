s=input()
if(s==s.upper()):
    print(s.capitalize())
elif(s[0]==s[0].lower() and s[1]==s[1].upper()):
    print(s.capitalize())
else:
    print(s)