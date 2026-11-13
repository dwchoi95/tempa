def fix_caps_lock(word):
    if word.isupper() or (word[1:].isupper() and word[0].islower()):
        return word.swapcase()
    else:
        return word

input_word = input()
print(fix_caps_lock(input_word))