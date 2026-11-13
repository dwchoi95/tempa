def process_word(word):
    if len(word) > 1 and word[1:].isupper():
        return word.swapcase()
    return word

if __name__ == "__main__":
    input_word = input().strip()
    result = process_word(input_word)
    print(result)