innitial=input()
innitials=[]
num=len(innitial)
for i in range(num):
    a=innitial[i]
    if a==a.upper():
        innitials.append(i)
if len(innitials)==num:
    print(innitial.title())
elif 0 not in innitials:
    num2=len(innitials)
    n=0
    for item in range(1,num):
        if item in innitials:
            n=n+1
    if n == num2:
        print(innitial.title())
    else:
        print(innitial)
else:
    print(innitial)