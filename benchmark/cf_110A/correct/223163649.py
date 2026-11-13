x=input()
ans=0
for z in range(len(x)):
  if '4'in x[z] or "7" in x[z]:
    ans=ans+1
if ans==4 or ans==7:
  print("YES")
else:
  print("NO")