p = str(input())
upp = 0
low = 0
for i in p:
    if i.isupper():
        upp += 1
    else: 
        low += 1

if (p[0].islower() and upp == len(p)-1):
    for i in range(len(p)):
        if i == 0:
            print(p[i].upper(), end="")
        else:
            print(p[i].lower(), end="")
elif upp == len(p):
    for i in range(len(p)):
        print(p[i].lower(),end="")
else:
    print(p)