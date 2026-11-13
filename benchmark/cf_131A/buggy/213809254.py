word = input()

if word.isupper() or word[1:].isupper():
    print(word.swapcase())
else:
    print(word)