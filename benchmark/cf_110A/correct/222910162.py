n = input()

counter = 0
ans = 'YES'

for i in range(len(n)):
    if n[i] == '4' or n[i] == '7':
        counter += 1

counter = str(counter)

for i in range(len(counter)):
    if counter[i] != '4' and counter[i] != '7':
        ans = 'NO'
        break

print(ans)