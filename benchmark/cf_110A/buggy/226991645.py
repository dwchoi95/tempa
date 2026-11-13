x = int(input())

x = str(x)
z = "YES"
fs = ff = False
for i in x:
    if(i!='7'and i!='4'):
        z = "NO"
        break
    else:
        if(i=='7'):
            fs = True
        else:
            ff = True
        
if(fs and ff):
    print(z)
else:
    print("NO")