n,m=list(map(int,input().split()))
a={}
for i in list(map(int,input().split())):
    if i in a:
        a[i]+=1
    else:
        a[i]=1
b=[]
for i in a:
    b.append([a[i],1])
b.sort()
for i in range(n):
    if b[-1][0]//b[-1][1]==0:
        print(0)
        break
    b[-1][1]+=1
    b.sort(key=lambda x:x[0]//x[1])
else:
    ans = min(b,key = lambda x:x[0]//(x[1]-1) if x[1]>1 else 10**5)
    print(ans[0]//(ans[1]-1))