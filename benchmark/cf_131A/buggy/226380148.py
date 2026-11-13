def process_word(word):
    if word.isupper():
        return word.lower()
    
    if word[1:].isupper():
        return word[0].lower() + word[1:].lower()
    
    return word

input_word = input().strip()
result = process_word(input_word)
print(result)