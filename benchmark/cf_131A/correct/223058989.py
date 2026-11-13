str=input()
#全都是大写
if str==str.upper():
    print(str.lower())
#第一个是小写
elif str[0]==str[0].lower() and str[1:]==str[1:].upper():
    print(str[0].upper()+str[1:].lower())
else:
    print(str)