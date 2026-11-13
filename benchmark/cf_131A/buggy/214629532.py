s = str(input())

if s[0].islower() == True and s[1:].isupper() == True:
    print(s[0].upper(),end="")
    print(s[1:].lower(),end="")
elif s.isupper() == True:
    print(s[0].upper(),end="")
    print(s[1:].lower(),end="")
else:
    print(s)