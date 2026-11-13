num = input()
count = 0
lucky_nums = ['4','7']
for i in range(len(num)):
  if num[i] in lucky_nums:
    count += 1
for j in range(len(str(len(num)))):
  if str(len(num))[j] not in lucky_nums:
    count -= 1
if count == len(num):
  print('YES')
else:
  print('NO')