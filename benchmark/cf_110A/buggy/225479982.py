n = int(input())
b = str(n)
arr= ['0','1','2','3','5','6','8','9']
arr2 = ['4','7']
count =0
for i in b:
    if i in arr2:
        count+=1
if count ==4 or count ==7:
    print('YES')
else:
    for i in b:
        if i in arr:
            print('NO')
            break
    else:
        print('YES')