n,m = map(int, input().strip().split(' '))
lst = list(map(int, input().strip().split(' ')))
res = list(dict.fromkeys(lst))
c=[]
for i in range(len(res)):
    c.append(lst.count(res[i]))
#print(c)
if m<n:
    print(0)
elif m==n:
    print(1)
else:
    m1=1
    c1=0
    j=2
    f=0
    while(True):
        c1=0
        for i in range(len(c)):
            c1+=c[i]//j
        if c1>=n:
            m1=j
            j+=1
        else:
            f=1
        if f==1:
            print(m1)
            break