word = input()
if word[1:].isupper():
    processed_word = word.swapcase()
else:
    processed_word = word
print(processed_word)