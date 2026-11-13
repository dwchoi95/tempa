n = input()
i = 0
sum1 = 0
sum2 = 0

indexes_4 = []
indexes_7 = []

for i, char in enumerate(n):
    if char == '4':
        indexes_4.append(i)
    elif char == '7':
        indexes_7.append(i)

indexes = indexes_4 + indexes_7

if len(indexes) == 4 or len(indexes) == 7:
    print("YES")
    
else:
    print("NO")