a = input()
if (a.count('7')+a.count('4')!=len(a)) :
    print("NO")
else:
    n = a.count('4') + a.count('7')
    if n==4 or n==7:
        print('YES')
    else:
        print('NO')