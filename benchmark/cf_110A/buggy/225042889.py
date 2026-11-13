skaitlis=input()

gar=len(skaitlis)
ja=0

for ja in range(gar):
    if(skaitlis[ja]==4) or (skaitlis[ja]==7):
        ja=ja+1
        print(ja, 'te')
if ja==4 or ja==7 or ja==gar-1:
    print('YES')
else:
    print('NO', ja, gar)