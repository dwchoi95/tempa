strli=input()
if strli.isupper():
    x=strli.lower()
    print(x)
elif strli[0].islower() and strli[1:].isupper():
    x=list(strli.lower())
    x[0]=x[0].upper()
    out="".join(x)
    print(out)
elif len(strli)==1 and strli[0].islower():
    x=strli.upper()
    print(x)
else:
    print(strli)