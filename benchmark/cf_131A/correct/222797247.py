word = input()
if(word == word.upper()):
    word = word.lower()
elif(word[0] == word[0].lower() and word[1:] == word[1:].upper()):
    word = word.capitalize()
print(word)