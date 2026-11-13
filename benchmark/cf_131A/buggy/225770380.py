my_word = input()

if ( my_word[0].islower() and my_word[1:].upper() )or my_word.upper():
    print(my_word[0].upper()+ my_word[1:].lower())
else:
    print(my_word)