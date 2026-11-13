a = input()
if a.count('4')==0 or a.count('7')==0 :
    print("NO")
else:
    n = a.count('4') + a.count('7')
    if n==4 or n==7:
        print('YES')
    else:
        print('NO')