a=input()
a=[str(i) for i in a]
count=sum(1 for i in range(1,len(a)) if a[i].isupper())
if count==len(a)-1:
    if a[0].isupper():
        a=[a[i].lower() for i in range(len(a)) ]
        print(''.join(a))
    else:
        print(a[0].upper()+''.join(a[i].lower() for i in range(1,len(a))))