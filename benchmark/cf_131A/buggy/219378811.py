word = input()

new_word = ""

if word[0].islower() and word[1:].isupper():

    new_word += word[0].upper()

    new_word += word[1:].lower()    

else:
    new_word = word
    
print(new_word)