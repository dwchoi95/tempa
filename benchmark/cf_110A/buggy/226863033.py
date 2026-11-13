num = input()
count = 0

for i in range(len(num)):
  if num[i] == '4' or num[i] == '7':
    count += 1
if count == len(num):
  print('YES')
else:
  print('NO')