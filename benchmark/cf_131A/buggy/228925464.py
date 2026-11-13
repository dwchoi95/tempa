word = input()

def should_capitalize(word):
    return word.isupper() or (word[0].isupper() and word[1:].islower()) or (word[0].islower() and word[1:].isupper())

if should_capitalize(word):
    print(word[0].upper() + word[1:].lower())
else:
    print(word)