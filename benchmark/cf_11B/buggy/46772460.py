n = int(input())
a = 0
st = 0
for i in range(1,n+1):
  if a <= n - i:
    a += i
    st += 1
  else:
    if a == n:
      print(st)
      exit()
    else:
      a += 1
      st += 2
print(st)