n=input()
s=len(n)
count4=0
count7=0
for i in range(0,s-1):
    if(n[i]==4 ):
        count4=count4+1
    if(n[i]==7):
        count7=count7+1
x=count4+count7        
if(count4==4 or count7==7 or x==4 or x==7):
    print("YES")
else:
    print("NO")