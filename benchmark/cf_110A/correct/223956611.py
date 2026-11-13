n=input()
x=str(n.count('4')+n.count('7'))
if x.count('4')+x.count('7')==len(x):
  print('YES')
else:
  print('NO')