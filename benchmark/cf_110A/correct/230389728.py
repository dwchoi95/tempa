n = input()

c = 0

for i in n:
    if(i in ['4','7']): c += 1

res = 'YES'

for i in str(c):
    if(not i in ['4','7']): 
        res = 'NO'

        break

print(res)