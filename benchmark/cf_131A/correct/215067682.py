a=input()
b=[x for x in a]
flag=0

for i in range(0, len(a)):
    if b[i].isupper():
        flag += 1
if (flag==len(a)-1 and b[0].islower()==True) or flag==len(a):
    print(a.swapcase())
else:
    print(a)