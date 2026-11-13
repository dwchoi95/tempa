n = input()

list1 = [int(i) for i in n]
f,s = list1.count(4),list1.count(7)

if (f+s)==len(n)==4 or 7:
    print('YES')
else:
    print('NO')