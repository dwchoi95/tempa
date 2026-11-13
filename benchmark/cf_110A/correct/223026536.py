array=list(input())
m=0
for i in range(0,len(array)):
    if array[i]=="4" or array[i]=="7":
        m+=1
a=list(str(m))
n=False
for i in range(0,len(a)):
    if a[i]!="4" and a[i]!="7":
        n=True
if n:
    print("NO")
else:
    print("YES")