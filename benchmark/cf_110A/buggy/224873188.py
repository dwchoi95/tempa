n=int(input())
m=str(n)
l1=len(m)
c=0
l=['1','2','3','5','6','8','9','0']
for num in m:
    if num not in l:
        c=c+1
    else:
        break
if c==l1:
    print("YES")
else:
    print("NO")