n = input()
if n.isupper():
  n = n.lower()
if n[1:].isupper():
  n = n.capitalize()
print(n)