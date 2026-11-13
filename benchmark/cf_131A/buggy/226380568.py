def process_word(word):
    if word.isupper() or (word[0].islower() and word[1:].isupper()):
        return word.swapcase()
    return word

input_word = input().strip()
result = process_word(input_word)
print(result)