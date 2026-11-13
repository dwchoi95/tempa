word = input()
if word == word.title():
  print(word)
else:
  string = ""
  for w in word:
    if w == w.upper():
      string += w.lower()
    else:
      string += w.upper()
  print(string)