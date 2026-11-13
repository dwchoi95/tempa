num = input()
count = 0
for i in num:
    if i == '4' or i == '7':
        count += 1

lucky = 'YES'
for i in str(count):
    if i == '4' or i == '7':
        pass
    else:
        lucky = 'NO'
        break
    
print(lucky)