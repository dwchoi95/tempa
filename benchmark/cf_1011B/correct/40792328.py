n,m=map(int,input().split())
arr=list(map(int,input().split()))
dict1={}
for i in range(m):
    try:
        dict1[arr[i]]+=1
    except:
        KeyError
        dict1[arr[i]]=1
arrx=[]
for i in dict1:
    arrx.append(dict1[i])
arrx.sort(reverse=True)
ans=0
if(m<n):
    print(0)
else:
    for i in range(1,arrx[0]+1):
        ans1=0
        for j in range(len(arrx)):
            ans1+=(arrx[j]//i)
        if(ans1>=n):
            ans=i
    print(ans)