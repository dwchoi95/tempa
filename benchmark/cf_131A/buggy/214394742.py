word = input()

if word.isupper() or word[1:].isupper():
    word = word.swapcase()

print(word)