word = input('')

def finder():
    if word.isupper():
        return word
    if word[0].islower() and word[1:].isupper():
        return word[0].upper() + word[1:].lower()
    if word[0].istitle():
        return word[0].upper() + word[1:].lower()



print(finder())