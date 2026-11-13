number = str(input())
numlist  = str(number).split()
x = 0
ans = 'YES'
for i in numlist:
    if i == '4' or i == '7':
        x += 1
x = str(x)
for i in x :
    if i != '4' and i!='7':
        ans == 'NO'

print(ans)