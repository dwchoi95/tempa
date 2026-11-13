x=input()

if len(x) ==1:
    print(x.upper())
elif x[0].islower() and x[1:].isupper():
    print(x[0].upper()+x[1::].lower())
elif x.isupper():
        print(x[0].upper()+x[1::].lower())
else:
    print(x)