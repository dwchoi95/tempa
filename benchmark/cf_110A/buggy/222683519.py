l=list(map(int,input().split()))
c=0
for i in l:
    if i!=4 or i!=7:
        print("NO")
        c=0
        break
    else:
        c=1
if c==1:
    print("YES")