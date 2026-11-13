a=input()
x=a[0]
flag=True
for i in range(len(a)):
    if "a"<=a[i]<="z" or "A"<=a[i]<="Z":
        continue
    else:
        flag=False
        break
if flag:
    print(x.upper()+a[1::].lower())
else:
    print(a)