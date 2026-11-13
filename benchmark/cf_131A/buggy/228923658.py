word = input()

def should_capitalize(word):
    return word.isupper() or (word[0].islower() and word[1:].isupper())

if should_capitalize(word):
    print(word.lower())
else:
    print(word)