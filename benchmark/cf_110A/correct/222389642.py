# Nearly Lucky Number

n = int(input())


a = n
residuos = []
while a>0:
    r = a%10
    a = a//10
    residuos.insert(0,r)

f_s = residuos.count(4)
s_s = residuos.count(7)

if (f_s + s_s)==4 or (f_s + s_s)==7:
    print('YES')
else:
    print('NO')