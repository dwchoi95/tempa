word = input()
if word.isupper() or (len(word) > 1 and word[1:].isupper()):
    print(word.swapcase())
else:
    print(word)