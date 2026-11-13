word=input()
n=0
for i in range(len(word)):
    if word[i]=='4' or '7':
        n+=1
    else:
        n+=0
if n==4 or 7:
    print('YES')
else:
    print('NO')