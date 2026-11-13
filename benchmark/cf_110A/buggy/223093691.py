inp=input()
st=''
for i in inp:
  if i=="4" or i =="7":
      st+=i
if len(inp)==len(st):
  print("YES")
else:
  print("NO")