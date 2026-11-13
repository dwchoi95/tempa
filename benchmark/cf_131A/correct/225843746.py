# h

My_word = input()

if My_word.isupper() or (My_word[0].islower() and My_word[1:].isupper()) or (len(My_word)==1 and My_word.islower()):
    My_word = My_word.swapcase()

print(My_word)