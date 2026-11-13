def process_word(word):
    if word.isupper() or word[1:].isupper():
        return word.swapcase()
    return word
word = input()
processed_word = process_word(word)
print(processed_word)