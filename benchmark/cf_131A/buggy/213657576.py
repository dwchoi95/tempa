x=input()
num=0
for i in range(len(x)):
        if x[i]>='a':
            num+=1
if num==1:
    print(x.swapcase())
    
elif x.isupper()==True:
    print(x.swapcase())
    pass

else:
    print(x)