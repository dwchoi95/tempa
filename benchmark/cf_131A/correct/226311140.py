old_word = input()
if old_word[1:] == old_word[1:].upper():
    new_word = ""
    for ch in old_word:
        if ch == ch.upper():
            new_word += ch.lower()
        else:
            new_word += ch.upper()
else:
    new_word = old_word
print(new_word)