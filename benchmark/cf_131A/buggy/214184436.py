word = input()

if len(word) == 1 and word.isupper():
    print(word.lower())
else:
    print(word)