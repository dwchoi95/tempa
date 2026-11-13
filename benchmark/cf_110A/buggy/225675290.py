a=input()
if len(set(a))<=2 :
    if len(set(a))==1 and sorted(set(a))[0]=='4' or sorted(set(a))[0]=='7':
        print('YES')
    elif len(set(a))==2 and sorted(set(a))[0]=='4' or sorted(set(a))[1]=='7':
        print('YES')
else:
    print('NO')