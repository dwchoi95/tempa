s = int(input())
c = 0
r = str(s)
for i in range(len(r)):
    if r[i] == '4' or r[i] == '7':
        c+=1
if c==len(str(s)):
    print('YES')
else:
    print('NO')