n=int(input())

dct={}
m=[]
def root(num):
    if(num<=9):
        return num
    if(num in dct.keys()):
        m.append(0)
        return dct[num]
    s=str(num)
    sm=0
    for i in s:
        sm=sm+int(i)
    dct[num]=root(sm)
    return dct[num]

dct1={}
dctn={}
for i in range(1,n+1):
    for j in range(1,n+1):
        x=root(i*j)
        if(x in dct1.keys()):
            if(i==1):
                dctn[x].append(j)
            dct1[x].append(i*j)
        else:
            if(i==1):
                dctn[x]=[j]
            dct1[x]=[i*j]

s=0
# print(len(m))
# print(dctn)
# print(dct1)
for i in dctn.keys():
    l=len(dctn[i])
    for j in dct1[i]:
       if(j not in dctn[i]):
           s=s+l
print(s)