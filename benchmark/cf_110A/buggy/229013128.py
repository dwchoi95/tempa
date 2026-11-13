a= input()
num=0
for i in a:
    if int(i)==4 or int(i)==7:
        num+=1
if num==len(a):
        print('YES')
else:
    print('NO')