old_word = input()
if old_word[1:] == old_word[1:].upper():
    new_word = old_word.capitalize()
else:
    new_word = old_word
print(new_word)