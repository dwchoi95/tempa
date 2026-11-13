from sys import stdin
from math import *

line = stdin.readline().rstrip().split()
n = int(line[0])
m = int(line[1])
nums = list(map(int, stdin.readline().rstrip().split()))

foodCant = [0] * 100
foodPeople = [0] * 100

for num in nums:
    foodCant[num-1]+=1


for i in range(n):
    maxRest = 0
    minRange = 0
    for j in range(100):
        if int(floor(foodCant[j]/(foodPeople[j]+1))) > maxRest:
            maxRest = int(floor(foodCant[j]/(foodPeople[j]+1)))
            minRange = j
    foodPeople[minRange] += 1

minFood = 1000
for j in range(100):
    if foodPeople[j] > 0 and int(floor(foodCant[j]/(foodPeople[j]))) < minFood:
        minFood = int(floor(foodCant[j]/(foodPeople[j])))
if minFood == 1000:
    print(0)
else:
    print(minFood)