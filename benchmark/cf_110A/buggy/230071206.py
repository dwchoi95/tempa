l=[4,7]
a=int(input(""))
n=0
k=1
while(a):
    b=a%10
    if b in l:
        n+=1
    a=int(a/10)
while(n):
    b=n%10
    if b in l:
        n=int(n/10)
        k=0
        continue
    k=1
    break
if k==0:
    print("YES")
else:
    print("NO")