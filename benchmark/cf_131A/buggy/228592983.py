word = input()

# Check if the word fits the condition for Caps Lock being on
if word[1:].isupper() or word.isupper():
    print(word.swapcase())  # Swap the case of all letters
else:
    print(word)  # Leave the word unchanged