def process_word(word):
    if word.isupper() or (word[0].isupper() and word[1:].islower()):
        processed_word = word.lower()
    else:
        processed_word = word

    return processed_word
word = input().strip()
result = process_word(word)
print(result)