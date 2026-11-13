word = input()

# Check if the word consists of only uppercase letters
if word.isupper():
    print(word.lower())

# Check if all letters except for the first one are uppercase
elif word[1:].isupper():
    print(word[0].lower() + word[1:].upper())

# If the word doesn't follow the rules, leave it unchanged
else:
    print(word)