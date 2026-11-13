from collections import Counter

n, m = input().split()  # n = participants, m = foods
n, m = int(n), int(m)

foods = Counter(map(int, input().split()))

maxPossible = m // n
if maxPossible == 0:
    print(0)

else:
    curMaxDay = 0
    for i in range(1,maxPossible+1):
        pplFed = 0
        for food in foods:
            numOfFood = foods[food]
            while numOfFood >= curMaxDay+1:
                numOfFood -= curMaxDay+1
                pplFed += 1
                if pplFed == n:
                    break
            if pplFed == n:
                break
        if pplFed == n:
            curMaxDay += 1
        else:
            break
    print(curMaxDay)