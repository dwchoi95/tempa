a = input()

c = 0

for i in a:
    if(i=='4' or i=='7'):
        c+=1
if(c==4 or c==7):
    print("Yes")
else:
    print("No")