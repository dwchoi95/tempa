word = input()
count = 0
for w in word:
  if w.upper() == w:
    count += 1

if count == len(word):
  print(word.lower())
elif count == 1 and word[0] == word[0].lower():
  print(word[0].upper() + word[1:].lower())
else:
  print(word)