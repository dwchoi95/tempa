def process_word(word):
    if word.isupper() or word[1:].islower():
        return word.swapcase()
    else:
        return word

def main():
    word = input().strip()  # Input word

    result = process_word(word)
    print(result)

if __name__ == "__main__":
    main()