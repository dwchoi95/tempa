word = input()

if word[0].islower():
    word = word[0].upper() + word[1:]
elif word.isupper() and word.isalpha():
    word = word[0] + word[1:].lower()
print(word)