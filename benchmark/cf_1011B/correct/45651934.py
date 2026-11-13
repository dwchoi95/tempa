from collections import Counter

param = input().split()
food_types = list(Counter(input().split()).values())

days = 1
people = int(param[0])
people_fed = sum(food_types)
while people_fed >= people:
    days += 1
    people_fed = 0
    for food in food_types:
        people_fed += food // days
print(days - 1)