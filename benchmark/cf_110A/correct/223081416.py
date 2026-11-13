l=list(input())
sum=0
for x in range(len(l)):
    if l[x]=='4' or l[x]=='7':
        sum+=1
s=list(str(sum))
sum2=0
for y in range(len(s)):
    if s[y]=='4' or s[y]=='7':
        sum2+=1
if sum2==len(s):
    print('YES')
else:
    print('NO')