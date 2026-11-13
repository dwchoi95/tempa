a=input()

if(a.upper()==a):
    print(a.swapcase())
elif(a.capitalize().swapcase()==a):
    print(a.swapcase())
else:
    print(a)