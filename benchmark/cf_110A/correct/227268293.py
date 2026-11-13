s=input()
a,b=0,0
for i in range(len(s)):
    if int(s[i])==4 or int(s[i])==7:
        a+=1
a=str(a)
for i in range(len(a)):
    if int(a[i])==4 or int(a[i])==7:
        b+=1
if b==len(a):
    print('YES')
else:
    print('NO')