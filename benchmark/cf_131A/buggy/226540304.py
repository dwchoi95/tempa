str=input()
if len(str) > 1:
    if str.upper()==str:
        str_final=str.lower()
    elif str[1:].upper()==str:
        str_final=str.title()
    else:
        str_final=str

else:
     str_final=str
print(str_final)