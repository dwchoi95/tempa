def caps(stri):
    count=0
    t=0
    for d in stri:
        if d in "A B C D E F G H I K L M N O P Q R S T V X Y Z ":
            count+=1
    if count==len(stri):
        return True
    if stri[0] not in "A B C D E F G H I K L M N O P Q R S T V X Y Z " and count==len(stri)-1:
        return True
    return False

s=input()
if caps(s):
    print(s.capitalize())
else:
    print(s)