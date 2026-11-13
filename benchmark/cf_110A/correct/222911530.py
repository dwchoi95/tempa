n = input()
count = 0
res = 'YES'
for i in range(len(n)):
    if n[i] == '4' or n[i] == '7':
        count += 1
count = str(count)
for i in range(len(count)):
    if count[i] != '4' and count[i] != '7':
        res = 'NO'
        break
print(res)