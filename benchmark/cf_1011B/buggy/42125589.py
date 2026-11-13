k,n=map(int,input().split())
m=list(map(int,input().split()))
m.sort()
m.reverse()
ans=1

def check(x):
    cc=x
    for i in m:
        cc-=i//x
        if cc<=0:
            return True
    return False

while check(ans):
    ans+=1
print(ans-1)