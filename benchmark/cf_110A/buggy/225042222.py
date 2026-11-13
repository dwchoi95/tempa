lucky = input()

count = 0
for i in lucky:
    if i == '4' or i == '7' :
        count = count + 1

if count == len(lucky):
    print('YES')
else :
    print('NO')