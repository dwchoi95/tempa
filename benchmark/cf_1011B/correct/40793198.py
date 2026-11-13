import copy
from collections import Counter


part_n,food_n = list(map(int,input().split()))


data = list(map(int,input().split()))
data_c =Counter(data)



data = []

for value in data_c.values():
    data.append(value)

best = 0

data_l = len(data)

for ndays in range(1,105):
    tmp = copy.deepcopy(data)
    happy = 0
    i = 0
    while i < data_l:
        if tmp[i] >= ndays:
            tmp[i] -= ndays
            happy += 1
        else:
            i +=1
        # if tmp[i] < ndays:
        #     break

    if happy< part_n:
        print(ndays-1)
        break