num = input()
count = 0
lucky_nums = ['4','7']


for i in range(len(num)):
  if num[i] in lucky_nums:
    count += 1

for number in str(count):
  if number not in lucky_nums:
    ans = 'NO'
  else:
    ans = 'YES'

print(ans)