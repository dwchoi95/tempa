n = input()

list1 = [int(i) for i in n]

count=0
for i in list1:
    if i==4 or i==7:
        count+=1

if len(list1)==count:
    if len(list1)==4 or len(list1)==7:
        print('YES')
    else:
        print('NO')
else:
    print('NO')