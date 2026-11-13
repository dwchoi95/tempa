n, m = map(int, input().split())
array = input().split()
array = [int(x) for x in array]
dict = dict()
for x in array : 
    if x in dict :
        dict[x] += 1
    else :
        dict[x] = 1
a = []
for x,y in dict.items() :
    a.append(y)

a = sorted(a)

changed = True
while changed :
    changed = False 
    i = 0
    while i < len(a)-1 :
        if a[i]+1<=a[i+1] :
            a[i]+=1
            a[i+1]-=1
            changed = True
        i+=1
a = sorted(a)
if len(a) == 1 :
    print(int(a[0] / n))
else :
    print(a[0])