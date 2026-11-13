n = int(input())
b = str(n)
arr= ['0','1','2','3','5','6','8','9']
for i in b:
    if i in arr:
        if len(b) ==4 or len(b) ==7:
            print('YES')
        else:
            print('NO')
        break
else:
    print('YES')