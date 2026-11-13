n,m = map(int,input().split())
import collections
food=collections.Counter(input().split())
food=dict(food)
#a.sort()

import operator
#a = {1: 2, 3: 4, 4: 3, 2: 1, 0: 0}
foodz = sorted(food.items(), key=operator.itemgetter(1), reverse=True)
food=[0]*len(foodz)
for i in range(len(foodz)):
    food[i]=foodz[i][1]

#print(food)
b=[0]*len(food)

b[0]=n
prev_days=food[0]//b[0]
min_days=prev_days
min_pos=0
for j in range(1,len(food)):
    good=False
    i=0
    while (i<j):
        if b[i]-1>=b[i+1]:
            #print(i,j)
            if b[i]>1:
                days=min(food[i]//(b[i]-1),
                food[j]//(b[j]+1))
                #print('days',days)
            else:
                days=-1


            if days>=prev_days:
                prev_days=days
                if (min_days>prev_days):
                   min_days=prev_days
                   if food[i]//(b[i]-1)<food[j]//(b[j]+1):
                      min_pos=i
                   else:
                      min_pos=j
                if (min_pos!=i)and(min_pos!=j):
                   prev_days=min_days
                b[i]-=1
                b[j]+=1
                #print(b)
                good=True
                i-=1
        i+=1
        
    if not(good):
        break
print(prev_days)