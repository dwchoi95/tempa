n = input()
c = n.count('4') + n.count('7')
if c == 0:
  print('NO')
else:
  while c > 0:
    r = c % 10
    if r != 4 and r != 7:
      print('NO')
      break
    c //= 10
  else:
    print("YES")