n = input()

list1 = [int(i) for i in n]
list2 = [4,7]
f,s = list1.count(4),list1.count(7)

if (f+s)==len(n) and len(n) in list2:
    print('YES')
else:
    print('NO')