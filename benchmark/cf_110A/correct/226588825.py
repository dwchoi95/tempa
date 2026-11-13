n = int(input())

s = 0
s += str(n).count('4')
s += str(n).count('7')

if str(s).count('4') + str(s).count('7') == len(str(s)):
    print('YES')
else:
    print('NO')