string=input()
char=list(string)
uppercase=1
for i in range (1,len(string)):
    if str(char[i]).islower()==True:
        uppercase=0
if uppercase==0:
    print(string)
else:
    print(string.swapcase())