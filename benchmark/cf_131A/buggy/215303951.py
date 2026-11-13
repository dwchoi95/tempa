def fix_caps_lock(word):
    if word.isupper():
        return word.lower()
    elif word[0].islower() and word[1:].isupper():
        return word.capitalize()
    else:
        return word

if __name__ == "__main__":
    input_word = input().strip()
    result = fix_caps_lock(input_word)
    print(result)