x=input()
for i in range(len(x)-1):
    if(x.isupper()):
        print(x.capitalize())
        break
    elif(x[0].islower() and x[i+1].isupper()):
        print(x.capitalize())
        break
    else:
        print(x)
        break