# hi

my_word = input()

if my_word.isupper() or (my_word[0].islower() and my_word[1:].isupper()) or (len(my_word)==1 and my_word.islower()):
    my_word = my_word.swapcase()

print(my_word)