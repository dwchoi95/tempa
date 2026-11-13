i=list(input())
s=set(i)
l=list(s)
if len(l)==2:
    if '4' in l and '7' in l:
        print('YES')
    else:
        print('NO')
else:
    c=0
    if '4' in l or '7' in l:
        for j in i:
            if j=='4' or j=='7':
                c+=1
        if c%4==0 or c%7==0:
            print('YES')
        else:
            print('NO')
    else:
        print('NO')