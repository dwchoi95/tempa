x = str(input())
u = 0
l = 0
for i in x:
    if i.isupper():
        u += 1
    else: 
        l += 1

if (x[0].islower() and u == len(x)-1):
    for i in range(len(x)):
        if i == 0:
            print(x[i].upper(), end="")
        else:
            print(x[i].lower(), end="")
elif u == len(x):
    for i in range(len(x)):
        print(x[i].lower(),end="")
else:
    print(x)