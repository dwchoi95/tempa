def correct_caps_lock(word):
    if word.isupper() or (word[0].islower() and word[1:].isupper()):
        return word.swapcase()
    return word

# Read the input word
word = input()

# Correct and print the result
result = correct_caps_lock(word)
print(result)