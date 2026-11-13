n=input("")
if len(n)>1:
    for x in n:
        if x!='4' and x!='7' :
            string="NO"
            break
        else:
            string="YES"
else:
    string="NO"
print(string)