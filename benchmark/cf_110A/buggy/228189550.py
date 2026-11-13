s=input()
l=(s.count('4')+s.count('7'))
if l==len(s) and (('7' in s )and ('4' in s)) or l==4 or l==7:
    print('YES')
else:
    print('NO')