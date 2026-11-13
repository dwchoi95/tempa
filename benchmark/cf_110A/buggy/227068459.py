a= input()
n = 0
if len(a) == 4 or len(a) == 7:
  print("YES")
else:
  for i in a:
    if i != "4" or i != "7":
      n+=1
  if n == 0:
    print("YES")
  else:
    print("NO")