word = input()
result = word[0].upper() + word[1:].lower() if (word.isupper() or word[1:].isupper()) else word
print(result)