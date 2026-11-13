word = input()

if word.isupper():
    processed_word = word.lower()

elif word[1:].isupper():
    processed_word = word.capitalize()

else:
    processed_word = word

print(processed_word)