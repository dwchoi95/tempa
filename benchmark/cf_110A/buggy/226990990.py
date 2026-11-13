x = int(input())

x = str(x)
z = "YES"
for i in x:
    if(i!='7'and i!='4'):
        z = "NO"
        break
print(z)