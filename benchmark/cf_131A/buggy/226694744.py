word = input()
if word[0].islower() and word[1:].isupper():
    result = word[0].upper() + word[1:].lower()
elif word.isupper() or word.islower():
    result = word.swapcase()
else:
    result = word
print(result)