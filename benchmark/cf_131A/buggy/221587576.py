string=input()
char=list(string)
uppercase=1
for i in range (1,len(char)):
    if char[i].isupper==False:
        uppercase==0

if uppercase==1:
    print(string.swapcase())
else:
    print(string)