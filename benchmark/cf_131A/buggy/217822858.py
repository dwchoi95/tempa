n = str(input())
if n.isupper() == True:
    print(n.lower().capitalize())
elif n[0:1].islower() == True and n[1:len(n)].isupper() == True:
    print(n.lower().capitalize())
else: print(n)