word = input()

if word.isupper():
    print(word.lower())
elif word[1:].isupper() and not word[0].isupper():
    print(word.lower().capitalize())
else:
    print(word)