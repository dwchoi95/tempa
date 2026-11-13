n = input()

def opposite(string):
    newString =("")
    for i in string:
        if i.islower():
            newString += i.upper()
        elif i.isupper():
            newString += i.lower()

    return newString

if n[0].islower() and n[1:].isupper():
    print(opposite(n))
elif n.isupper():
    print(opposite(n))
else:
    print(n)