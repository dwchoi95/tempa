skaitlis=input()

gar=len(skaitlis)
ja=0

for i in range(gar):
    if(skaitlis[i]=='4') or (skaitlis[i]=='7'):
        ja=ja+1
        #print(ja)

if ja==4 or ja==7 or ja==gar-1:
    print('YES')
else:
    print('NO')