n = int(input())
b = str(n)
arr2 = ['4','7']
count =0
for i in b:
    if i in arr2:
        count+=1
if count ==4 or count ==7:
    print('YES')
else:
    print('NO')