n_m = input()
n_m = n_m.split(' ')
n_m = list(map(int, n_m))

n = n_m[0] #passanger
m = n_m[1] #foods stock
#print(n_m)

foods = input()
foods = foods.split(' ')
foods = list(map(int, foods))
foods = sorted(foods, reverse=True)
#print(foods)

foods_count = []
temp = 1

#print(len(foods_count))

#counting for each
for i in range(0,len(foods)-1):
    if foods[i] == foods[i+1]:
        temp = temp + 1
    else:
        #print(temp)
        foods_count.append(temp)
        temp = 1
#print(temp)
foods_count.append(temp)
foods_count = sorted(foods_count, reverse=True)
#print(foods_count)

divisor = 1
result = 0
status = 0

while status == 0:
    result = 0

    for j in range(0,len(foods_count)):
        result = result + (foods_count[j] // divisor)

    if result < n:
        status = status + 1
    else:
        divisor = divisor + 1

print(divisor - 1)