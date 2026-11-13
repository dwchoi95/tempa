word = input()
if len(word)==1:
    if word.islower() == True:
        print(word.upper())
elif (word[0].islower() == True and word[1:].isupper() == True):
    print(word.capitalize())
elif (word.isupper()==True):
    print(word.lower())
else:
    print(word)