a=input()
cnt=0
clk=1
for i in a:
    if i=='4' or i=='7':
        cnt=cnt+1
cnt=str(cnt)
for i in cnt:
    if i=='4' or i=='7':
        continue
    else:
        print("NO")
        clk=0
        break
if clk==1:
    print("YES")