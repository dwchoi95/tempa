word = input()
if word[0].upper() or word[1:].lower():
    print(word)
else:
    print(word.capitalize())