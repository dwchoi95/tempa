word = input()
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    result = word.swapcase()
else:
    result = word
print(result)