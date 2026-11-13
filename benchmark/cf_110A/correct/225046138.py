number = input()
lucky_number = number.count('4') + number.count('7')
if lucky_number == 4 or lucky_number == 7:
  print("YES")
else:
  print("NO")