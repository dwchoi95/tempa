n = int(input())
o = 0
i = 0
while True:
  if o >= n and o % 2 == n % 2:
    print(i)
    break
  else:
    i += 1
    o += i