str=input()
if str[0].islower() and str[1].isupper():
    str_final=str.title()
elif str.isupper():
    str_final=str.title()
else:
    str_final=str
print(str_final)