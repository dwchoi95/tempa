# Read input
word = input()

# Function to check if a word meets the Caps Lock rule
def meets_caps_lock_rule(word):
    return word.isupper() or (word[0].islower() and word[1:].isupper())

# Apply the Caps Lock rule if the word meets the criteria
if meets_caps_lock_rule(word):
    result = word.swapcase()  # Swap the case of all letters
else:
    result = word  # Leave the word unchanged

# Print the result
print(result)