s=input()
if(s[0].isupper() and s[1:len(s)].islower()):
    print(s)
else:
    print(s.swapcase())