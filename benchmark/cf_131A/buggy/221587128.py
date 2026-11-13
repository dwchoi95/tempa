def fix_capslock(word):
    if word.isupper() or (word[0].islower() and word[1:].isupper()):
        return word.swapcase()
    else:
        return word
word=input()
res=fix_capslock(word)
print(res)