n = input()
c = []
for i in range(len(n)):
    c.append(n[i])
    
cnt = 0
for i in c:
    if i == '4' or i == '7':
        cnt+=1
        
if cnt == len(c):
    print('YES')

else:
    print('NO')