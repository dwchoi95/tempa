a=input()
j=list(a)
l=[]
ll=[]
l.append(j[0])
for i in range (len(j)):
    ll.append(j[i])
ll.remove(ll[0])
bb=("").join(ll)
ee=("").join(l)
if(ee==ee.upper() or ee==ee.lower() and bb==bb.upper() ):
    print(ee.upper()+bb.lower())
else:
    print(a)