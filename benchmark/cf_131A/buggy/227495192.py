string = input()
if string.isupper or string[1:].isupper:
    print(string[0].upper()+string[1:].lower())
else:
    print(string)