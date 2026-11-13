a= input()
n = 0
m = 0
for i in a:
  if i != "4" and i != "7":
    n+=1
  else:
    m+=1
if n == 0:
  print("YES")
else:
  if m == 4 or m == 7:
    print("YES")
  else:
    print("NO")