word = input()
if word.isupper() or word[1:].islower():
    result = word.capitalize()
    print(result)
else:
    print(word)