y=input()
luckyamount=0
for x in y:
  if x=='7' or x=='4':
    luckyamount=luckyamount+1
if luckyamount==4 or luckyamount==7:
  print("YES")
else:
  print("NO")