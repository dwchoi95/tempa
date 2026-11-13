from collections import Counter
    
n,m=list(map(int,input().split()))
packets=list(map(int,input().split()))
packets=dict(Counter(packets))
val=packets.values()

#print(list(val))
i=1
while(True):
    sum=0
    for j in val:
        sum+=int(j/i)
    if(sum<n):
        break
    i+=1
print(i-1)