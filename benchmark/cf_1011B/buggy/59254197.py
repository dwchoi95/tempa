from collections import Counter

def chk(L,n):
    sum=0
    for i in L:
        sum+=int(i/n)
    #return sum
    
    if(sum>=n):
        return (True,sum)
    else:
        return (False,sum)
    
n,m=list(map(int,input().split()))
packets=list(map(int,input().split()))
packets=dict(Counter(packets))
val=packets.values()

#print(list(val))
res=(True,0)
i=1
while(res[0]!=False):
    res=chk(val,i)
    if(res[0]==False):
        print(i-1)
    #print(res)
    i+=1