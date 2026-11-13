word=input()

if (word[1:-1].isupper() and word[0].islower()) or word.isupper():
  word=word.casefold()
  word=word.capitalize()
print(word)