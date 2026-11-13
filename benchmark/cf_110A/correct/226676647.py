list1=list(str(input()))
n=list1.count('4')+list1.count('7')
if n!=0 and (n==4 or n==7):
    print('YES')
else:
    print('NO')