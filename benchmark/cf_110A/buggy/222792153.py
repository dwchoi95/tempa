n = input()
m = 0
c = 0
for i in n:
  if i == '7' or i=='4':
    m += 1
  c += 1
if m == c:
  print('YES')
else:
  print('NO')