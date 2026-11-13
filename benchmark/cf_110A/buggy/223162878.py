a=int(input())
x=[i for i in str(a)]
if x.count('4')+x.count('7')==len(x):
    print('YES')
else:
    print('NO')