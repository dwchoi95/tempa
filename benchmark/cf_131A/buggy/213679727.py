word = input()
if((word[0].islower() and word[1:].isupper()) or word.isupper()):
    word = word[0].upper() + word[1:].lower()
print(word)