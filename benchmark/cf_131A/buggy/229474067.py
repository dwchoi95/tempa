word = input() # get user input

if word.isupper(): # check if all letters are uppercase
    print(word.lower()) # change to all lowercase
elif word[1:].isupper(): # check if all letters except first are uppercase
    print(word[0] + word[1:].lower()) # change all except first letter to lowercase
else:
    print(word)