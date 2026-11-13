a=input()
k=0
for i in range(1,len(a)):
    if a[i].upper()==a[i]:
        k=k+1
if k==(len(a)-1):
    a=a.swapcase()
print(a)