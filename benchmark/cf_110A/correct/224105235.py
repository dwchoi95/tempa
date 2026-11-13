cnt=0
lucky=str(input())

for x in lucky:
  if x=='7' or x=='4':
    cnt=cnt+1

if cnt==7 or cnt==4:
  print('YES')
else:
  print('NO')