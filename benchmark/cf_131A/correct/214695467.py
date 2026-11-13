word = input()
result = ''
if len(word) == 1 and word.islower():
    result = word.upper()
elif word.isupper() or (word[0].islower() and word[1:].isupper()):
    result = word.swapcase()
else:
    result = word

print(result)