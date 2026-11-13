s = input()
if s.isupper() == True:
    print(s.swapcase())
elif s[0].islower() == True and s[1::].isupper() == True:
    print(s.swapcase())
else:
    print(s)