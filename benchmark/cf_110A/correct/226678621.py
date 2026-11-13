a=[int(i) for i in list(input())]
ct=0
for i in a:
    if i==4 or i==7:
        ct+=1
b=[int(i) for i in list(str(ct))]
b_luck=True
for i in b:
    if i!=4 and i!=7:
        b_luck=False
if b_luck:
    print('YES')
else:
    print('NO')