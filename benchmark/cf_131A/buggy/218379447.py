word=input()

if (word[1:-1].isupper() and word[0].islower()):
  word=word.casefold()
  word=word.capitalize()
if word.isupper():
  word=word.casefold()
if len(word)==1 and word.islower():
  word=word.upper()
print(word)