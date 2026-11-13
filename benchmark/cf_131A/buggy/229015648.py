def fix_capslock(word):
    if word.isupper() or word[1:].isupper():
        return word.swapcase()
    else:
        return word

# Read the input word
input_word = input().strip()

# Apply the rule and print the result
result = fix_capslock(input_word)
print(result)