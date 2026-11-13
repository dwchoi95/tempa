x=input()

if x==x.upper():

    print(x.lower())

elif x[1:]==x[1:].upper():

    print(x[0].upper()+x[1:].lower())

else:

    print(x)