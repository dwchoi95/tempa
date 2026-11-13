k,n=map(int,input().split())
b=list(map(int,input().split()))
m=[]
c=0
for i in range(102):
    m.append(0)
for i in b:
    m[i]+=1
l=0
r=101
def can(w):
    c=0
    if max(m)//k>=w:
        return 1
    for i in range(len(m)):
        if m[i]>=w:
            c+=m[i]//w
    if c>=k:
        return 1
    else:
        return 0
while r>l:
    w=(l+r)//2
    if can(w): l=w+1
    else: r=w
print(r-1)