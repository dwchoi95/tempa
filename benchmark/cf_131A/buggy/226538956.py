s=input()
if s[0].isupper():
  a=s[1:].lower()
  print(s[0]+a)
elif s[0].islower():
  a=s[1:].lower()
  b=s[0].upper()
  print(b+a)