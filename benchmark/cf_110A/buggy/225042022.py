skaitlis=input()

gar=len(skaitlis)
ja=0

for i in range(gar):
    if(skaitlis[i]==4) or (skaitlis[i]==7):
        ja=ja+1
if ja==4 or ja==7:
    print('YES')
else:
    print('NO')