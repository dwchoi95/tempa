import operator

p,f=map(int,input().split())
foods = list(map(int,input().split()))

fc = {}
for i in foods:
    if i not in fc:
        fc[i]=foods.count(i)
foods=set(foods)
counts = {}
for i in foods:
    counts[i]=0
maxDays={}

for i in foods:
    maxDays[i]=fc[i]

for i in range(p):
    key = max(maxDays.items(), key=operator.itemgetter(1))[0]
    counts[key]+=1
    maxDays[key]=int(fc[key]/(counts[key]+1))
    
for i in list(foods):
    if counts[i]==0:
        foods.remove(i)

print(min([int(fc[i]/counts[i]) for i in foods]))