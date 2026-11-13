word = input()

if word.isupper() or word[1:].isupper():
   corrected_word = word.swapcase()
else:
    corrected_word = word
print(corrected_word)