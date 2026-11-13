s = input().strip()
if s.isupper():
   print(s.lower())
elif(s[0].islower() and (not s[1:] or s[1:].isupper())):
   print(s.capitalize())
else:
   print(s)