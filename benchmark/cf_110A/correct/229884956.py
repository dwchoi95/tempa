n = input()
c = []
for i in range(len(n)):
    c.append(n[i])
    
cnt = 0
for i in c:
    if i == '4' or i == '7':
        cnt+=1
        
k = 0 
cnt = str(cnt)
for i in range(len(cnt)):
    if cnt[i] == '4' or cnt[i] == '7':
        k+=1
        
if k == len(cnt):
    print('YES')

else:
    print('NO')