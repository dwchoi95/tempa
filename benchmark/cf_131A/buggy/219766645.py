word = input()

if (len(word) == 1 and word.islower()) or \
    word.isupper() or (word[0].islower() and word[1:].isupper()): word = word.capitalize()
elif word.isupper(): word = word.lower()
print(word)