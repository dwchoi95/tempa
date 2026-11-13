s = input()
if s.isupper()or s[1:].isupper():
    print(s.swapcase())
else:
    print(s)