s = input()
c = 0
for i in range(len(s)):
  if s[i].isupper():
    c += 1
if c == len(s):
  print(s.lower())
else:
  if s[0].islower():
    print(s.swapcase())
  else:
    print(s)