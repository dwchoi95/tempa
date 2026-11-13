string = input()

if string[0].lower() == string[0]:
  if string[1:].upper() == string[1:]:
    print(string.capitalize())
  else:
    print(string)
elif string.upper() == string:
  print(string.capitalize())
else:
  print(string)