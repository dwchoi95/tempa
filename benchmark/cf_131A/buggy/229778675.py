txt = input()
if txt.isupper(): # T -> t | one letter case
    print(txt.lower())
elif txt[0].islower and txt[1:].isupper:
    print(txt[0].upper() + txt[1:].lower())
else:
    print(txt)