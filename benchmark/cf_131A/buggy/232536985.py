word = input()

if word.isupper() == True or word[0].islower() == True and word[1:].isupper() == True:
    print(word.capitalize())
else:
    print(word)