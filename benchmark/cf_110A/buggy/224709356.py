n=input()
c=0
m=0
for i in range(len(n)):
    if(n[i] != '4' and n[i] != '7'):
        c+=1
    else:
        m+=1 
if(c > 0):
    print("no")
elif(m >= 1):
    print("yes")