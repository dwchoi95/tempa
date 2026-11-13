a=input()

n=a.count('4')+a.count('7')

s=str(n)

if n==0:

    print('NO')

    exit()

if s.count('4')+s.count('7') == len(s):

    print('YES')

    exit()

print('NO')