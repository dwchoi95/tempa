n=input()
if len(n) == 1 or n.isupper() == True or n[0:1].islower() and n[1:len(n)].isupper():
    print(n.swapcase())
else: print(n)