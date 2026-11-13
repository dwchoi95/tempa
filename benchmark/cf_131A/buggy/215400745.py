x=input()
if(x[0]==x[0].lower()):
    print(x[0].upper()+x[1:len(x)].lower())
else:
    print(x)