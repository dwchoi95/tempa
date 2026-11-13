n = input()
cnt = 0
for char in n:
  if char == '4' or char == '7':
    cnt += 1
for char in str(cnt):
  if char != '4' and char != '7':
    print('NO')
    break
else:
  print('YES')