x= input()
y=""
if x==x.upper():
    print(x)
else:
    y+=x[0].upper()
    y+=x[1:len(x)].lower()
    print(y)