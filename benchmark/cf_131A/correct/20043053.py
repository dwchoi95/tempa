s = input()

if (len(s) == 1 or s.isupper() or (s[0].islower() and s[1:].isupper())):

    print(s.swapcase())

else:

    print(s)