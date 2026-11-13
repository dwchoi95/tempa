def word_change(word):
    if word.isupper() or word[0].islower() and word[1:].isupper():
        return word.swapcase()
    else:
        return word
        
word = input()
res = word_change(word)
print(res)