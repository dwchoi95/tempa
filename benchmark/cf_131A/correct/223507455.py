word = input()
if len(word) == 1:
    word = word.swapcase()
elif word[1:].isupper():
    word = word.swapcase()
else:
    word = word
print(word)