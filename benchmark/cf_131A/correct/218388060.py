x=input()
if(len(x)==1 or x.isupper()==True or x[0:1].islower()==True and x[1:len(x)].isupper()==True):
    print(x.swapcase())
else:
    print(x)