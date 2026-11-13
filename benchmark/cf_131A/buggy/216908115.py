v=input()
if v[0].lower()+v[1::].upper():
    print(v)
else:
  print(v[0].upper()+v[1::].lower())