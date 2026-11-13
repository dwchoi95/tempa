my_word = input()

if my_word[0].islower():
    print(my_word[0].upper()+ my_word[1:].lower())
else:
    print(my_word)