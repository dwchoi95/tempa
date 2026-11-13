def apply_caps_lock_rule(word):
    # Check if the word only contains uppercase letters or
    # if all letters except the first one are uppercase
    if word.isupper() or word[1:].isupper():
        # Change the case of all letters in the word
        return word.swapcase()
    else:
        # Leave the word unchanged
        return word

# Read the input word
input_word = input()

# Apply the Caps lock rule and print the result
result = apply_caps_lock_rule(input_word)
print(result)