def apply_caps_lock_rule(word):
    # Check if the word only contains uppercase letters
    if word.isupper():
        return word.lower()
    
    # Check if all letters except for the first one are uppercase
    if word[1:].isupper():
        return word[0] + word[1:].lower()

    return word

# Read the input word from the user
word = input().strip()
result = apply_caps_lock_rule(word)
print(result)