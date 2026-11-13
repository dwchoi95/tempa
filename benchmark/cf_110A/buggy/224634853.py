n=int(input())
res=[]
final="YES"
while(n>0):
    x=n%10
    res.append(x)
    n=n//10

for i in res:
    if(i not in [7,4]):
        final="NO"
    break

print(final)