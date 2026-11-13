a=input()
x=[*a]
if '4' or '7' in x:
    if len(x)==4 or len(x)==7:
        print("Yes")
    else:
        print("No")
else:
    print("No")