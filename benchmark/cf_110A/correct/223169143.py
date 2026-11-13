l=input()
cnt=0
c=1

for i in l:

    if i=='4' or i=='7':
        cnt=cnt+1
cnt=str(cnt)

#####
for i in cnt:
    if i=='4' or i=='7':
        continue
    else:
        print("NO")
        c=0
        break
if c==1:
    print("YES")