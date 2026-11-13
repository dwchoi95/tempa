n,m=map(int,input().split())
FOOD=list(map(int,input().split()))

FOODlist=[0 for i in range(101)]

for i in range(m):
    FOODlist[FOOD[i]]+=1
    
FOODlist.sort(reverse=True)

last=FOODlist.index(0)
FOODlist=FOODlist[:last]
#print(FOODlist)


day=0

while True:
    checkday=day+1
    checkpeople=n

    for i in range(len(FOODlist)):
        checkpeople=checkpeople-FOODlist[i]//checkday

    if checkpeople<=0:
        day+=1
    else:
        break

print(day)