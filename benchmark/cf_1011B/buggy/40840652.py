s=input().split(' ')
n,m=[int(s[i]) for i in range(0,2)]
s=input().split(' ')
a=[int(s[i]) for i in range(0,m)]
a.sort()
b=[[a[0],1],]
j=0
for i in range(1,len(a)):
    if (a[i]==a[i-1]):
        b[j][1]+=1
    else:
        j+=1
        b+=[[a[i],1],]
b.sort(key=lambda i:i[1])
c=[]
for i in range(0,len(b)):
    c+=[b[i][1]]
l=len(c)
find=False
res=0
for i1 in range(100,0,-1):
    d=[]
    d+=c
    i2=0
    for i3 in range(0,n):
        if (d[i2]-i1>=0):
            d[i2]-=i1
        elif (i2+1<l):
            i2+=1
            if (d[i2]-i1>=0):
                d[i2]-=i1
            else:
                break
        else:
            break
    else:
        find=True
        res=i1
        break
print(res)