import sys
s=list(sys.stdin.readline())[:-1]
happy=s.count('7')+s.count('4')
if happy in [4,7]:
    print('YES')
else:
    print('NO')