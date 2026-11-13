word=input()
x=""
if word[0].islower()==True and word[1:len(word)].isupper()==True:
   x=(word[0].upper()+word[1:len(word)].lower())
   print(x)
elif word[0:len(word)].isupper==True:
    x=word[0].upper()
    x+=word[1:len(word)].lower()
    print(x)
else:
    print(word)