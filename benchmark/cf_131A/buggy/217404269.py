word = input()

if word[0].islower() and word.isalpha() and word[1:].isupper():
    word = word[0].upper() + word[1:].lower()
elif word.isupper() and word.isalpha():
    word = word[0] + word[1:].lower()

print(word)