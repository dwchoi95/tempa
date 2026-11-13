x="YES"
c=input()
for i in range(len(c)):
    if(c[i]=='4' or c[i]=='7'):
        continue
    else:
        x="NO"
        break
print(x)