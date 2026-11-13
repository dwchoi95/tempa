user = str(input())
counter = 0
for i in user:
  if i == '4' or i == '7':
    counter += 1
counter = str(counter)
for i in counter:
  if i == '4' or i == '7':
    continue
  else:
    print('NO')
    break
else:
  print('YES')