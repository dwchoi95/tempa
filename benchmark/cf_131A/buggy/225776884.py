word = input()
if word.isupper() or (len(word) > 1 and word[1:].islower()):
    result = word.swapcase()
    print(result)
else:
    print(word)