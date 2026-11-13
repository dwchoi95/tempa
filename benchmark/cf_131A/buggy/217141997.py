def fix_caps_lock(word):
    if word.isupper() or word[1:].isupper():
        return word.swapcase()
    return word

# Read input
word = input()

# Apply the rule and print the result
result = fix_caps_lock(word)
print(result)