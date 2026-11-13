n=input()
print(n)
a=b=0
for i in range(len(n)):
    if n[i]=='4' or n[i]=='7': a+=1
    else: b+=1
if b==0 or a==(4 or 7):
    print('YES')
else: print('NO')