n = input()
if n.isupper() or n[1:].isupper():
  n = n.swapcase()
  print(n)