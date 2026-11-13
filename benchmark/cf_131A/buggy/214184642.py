word = input()

if len(word) == 1 or (len(word) > 1 and word[1:].islower()):
    result = word.swapcase()
else:
    result = word

print(result)