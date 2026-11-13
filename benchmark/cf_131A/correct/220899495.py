word = input()

if word.isupper() or (word[0].islower() and word[1:].isupper()) or (len(word)==1 and word.islower()):
    print(word.swapcase())
else:
    print(word)