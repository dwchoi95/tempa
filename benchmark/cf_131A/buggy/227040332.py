def caps_lock(word):
    if word.isupper() or word[1:].islower():
        return word.swapcase()
    else:
        return word
word = input()
result =caps_lock(word)
print(result)