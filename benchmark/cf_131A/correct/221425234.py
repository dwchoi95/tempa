n=input()
a=len(n)
if a==1 and n.islower():
    print(n.upper())
elif n.isupper():
    print(n.lower())
elif n[0].islower and n[1::].isupper():
    print(n[0].upper()+n[1::].lower())
else:
    print(n)