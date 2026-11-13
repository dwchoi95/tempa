word = input()

if word[1:].isupper():
    print(word.lower().capitalize())
else:
    print(word)