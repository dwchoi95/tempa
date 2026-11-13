word = input()
if word.upper() == word:
    print(word.lower())
elif word[0].lower() == word[0] and word[0].upper() + word[1:] == word.upper():
    print(f"{word[0].upper()}{word[1:].lower()}")
else:
    print(word)