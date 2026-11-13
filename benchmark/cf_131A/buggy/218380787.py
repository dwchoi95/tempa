word=input()

if (word[1:-1].isupper() and word[0].islower()):
  word=word.casefold()
  word=word.capitalize()
  print(word)
elif word.isupper():
  word=word.casefold()


elif len(word)==1 :
   if word.islower():
       word=word.upper()
       print(word)
   else:
       word=word.lower()
print(word)