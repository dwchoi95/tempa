x= input()
y=""
if x==x.upper():
    print(x.lower())
elif x[0].lower()==x[0] and x[1:len(x)].upper()==x[1:len(x)]:
    y+=x[0].upper()
    y+=x[1:len(x)].lower()
    print(y)
else:
    print(x)