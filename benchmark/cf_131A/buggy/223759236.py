word = input()
if word.isupper():
    word = word.lower()
elif word[1:].isupper() and word[0].islower():
    word = word[0].upper()+word[1:].lower()
print(word)