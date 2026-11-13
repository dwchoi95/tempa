t=input()
if (len(t)==1):
    t=t.swapcase()
elif (t.isupper() or t[0].islower() and t[1:].isupper()):
    t=t.swapcase()
print(t)