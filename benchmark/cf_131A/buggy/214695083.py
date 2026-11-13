word = input()
if len(word) == 1 and word.islower():
    ans = word.swapcase()
    print(ans)
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    result = word.swapcase()
else:
    result = word

print(result)