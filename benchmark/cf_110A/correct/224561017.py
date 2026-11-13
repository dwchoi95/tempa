number = input()
luckyCounter = 0
for i in range(0,len(number)):
  z = int(number[i]) == 4
  y = int(number[i]) == 7
  if z == True:
      luckyCounter += 1
  elif y == True:
    luckyCounter +=1

if luckyCounter == 4:
  print("YES")
elif luckyCounter == 7:
  print("YES")
else:
  print("NO")