w=int(input())
p=0
i=1
s=0
for i in range(1,10000):
    s=s+1
    if p+i==w:
        print(s)
        break
    elif p+i>w:
        p=p-i
    else:
        p=p+i