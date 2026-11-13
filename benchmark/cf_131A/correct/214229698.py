string=input()
if (string.isupper() or (string[0].islower() and (string[1:].isupper() or len(string)==1))):
    print(string.swapcase())
else:
    print(string)