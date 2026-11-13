n,k=map(int,input().split())
s=list(map(int,input().split()))
val=[ 0 for i in range(105) ]
for i in s:
    val[i]+=1

def check(day) :
    ak=0
    for i in val:
        ak+=i//day
    if ak>=n:
        return 1
    else:
        return 0
ans=1
if check(ans):
    while check(ans)==1 :
        ans+=1
    print(ans-1)
else:
    print("0")