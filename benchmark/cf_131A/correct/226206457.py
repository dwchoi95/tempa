word = str(input())

if word.upper() == word: print(word.lower())
elif word[1:].upper() == word[1:]: print(word.title())
else: print(word)