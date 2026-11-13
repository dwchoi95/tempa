word = input()

if word.isupper() or (len(word) == 1 and word.islower()):
    print(word.swapcase())
else:
    print(word)