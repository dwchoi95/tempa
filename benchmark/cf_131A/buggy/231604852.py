str = input()
new_str = ""
if 1<=len(str)<=100:
  if 65<=ord(str[0])<=90:
    new_str = str[0]
  elif 97<=ord(str[0])<=122:
    new_str = chr(ord(str[0])-32)
  for i in range(1, len(str)):
    if 65<=ord(str[i])<=90:
      new_str += chr(ord(str[i])+32)
    elif 97<=ord(str[i])<=122:
      new_str += str[i]
print(new_str)