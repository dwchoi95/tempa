word = input()
if len(word) == 1 and word.islower():
    print(word.upper())
elif len(word) > 1 and word[1:].isupper():
    print(word.swapcase())
else:
    print(word)