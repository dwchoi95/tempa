word = input()
result = word.swapcase() if word.isupper() or word[1:].islower() else word
print(result)