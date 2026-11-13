str = input()
counter = 0
new_str = ""
if 1<=len(str)<=100:
  for i in range(0, len(str)):
    if 65<=ord(str[i])<=90:
      counter += 1
if counter == len(str):
  if 65<=ord(str[0])<=90:
    new_str += str[0]
  elif 97<=str[0]<=122:
    new_str += chr(ord(str[0])-32)
  for i in range(1, len(str)):
    if 65<=ord(str[i])<=90:
      new_str += chr(ord(str[i])+32)
    elif 97<=str[i]<=122:
      new_str += str[i]
elif counter==len(str)-1:
  if 97<=ord(str[0])<=122:
    new_str += chr(ord(str[0])-32)
    for i in range(1, len(str)):
      if 65<=ord(str[i])<=90:
        new_str += chr(ord(str[i])+32)
      elif 97<=str[i]<=122:
        new_str += str[i]
else:
  print(str)
print(new_str)