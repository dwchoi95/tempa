word = input()
result = word.upper() if word.islower() or (word[0].islower() and word[1:].isupper()) else word
print(result)