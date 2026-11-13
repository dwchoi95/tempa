l1=['4','7']
l3=['7','4']
s1=input()
l2=[]
for i in s1:
    if i not in l2:
        l2.append(i)
if l1==l2 or l2==l3:
    print('YES')
else:
    print('NO')