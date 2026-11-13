import collections
inp = list(map(int, input().split(' ')))
typ = input().split(' ')
count=[]
day = 1
while True:
    for i in collections.Counter(typ).values():
        if int(i/day):
            count.append(int(i/day))
    if sum(count)>=inp[0]:
        count=[]
        day+=1
    else:
        day-=1
        break
print(day)