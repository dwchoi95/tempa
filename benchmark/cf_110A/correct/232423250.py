n = input()
count = 0
output = 'YES'
for index in range(len(n)):
    if (int(n[index]) == 7 ) | (int(n[index]) == 4 ):
        count += 1
if (count == 7 ) | (count==4 ):
    output = 'YES'
else :
    output = 'NO'

print(output)