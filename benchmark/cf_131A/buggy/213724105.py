strr = input()
k = True
for i in range(1, len(strr)):
    if strr[i].islower():
        k = False
if k == True:
    s = ''
    for i in range(len(strr)):
        if strr[i].islower():
            s += strr[i].upper()
        else:
            s += strr[i].lower()
    print(s)
print(strr)