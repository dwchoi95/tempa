people_quantity, food_package_quantity = map(int, input().split())
food_type_sequence = list(map(int, input().split()))

food_type_quantity_sequence = [0]*101

for i in food_type_sequence:
    food_type_quantity_sequence[i] += 1

# For d days, maximum how many people can go?

for day in range(food_package_quantity, -1, -1):
    max_people_possible = 0
    if day == 0:
        print(0)
        break
    for food_type_quantity in food_type_quantity_sequence:
        max_people_possible += food_type_quantity // day
    if max_people_possible >= people_quantity:
        print(day)
        break