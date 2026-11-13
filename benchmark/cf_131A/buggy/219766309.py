word = input()

if word.islower(): word = word.upper()
elif word.isupper(): word = word.lower()
elif word[0].islower() and word[1:].isupper(): word = word.capitalize()

print(word)