n=input()
if len(n)==1 and n.isupper():
    print(n.lower())
elif n.isupper():
    print(n.lower())
elif n[0].islower() and n[1:].isupper():
    print(n.swapcase())
else:
    print(n)