def c(word):
    if word.isupper() or (word[1:].isupper() and word[0].islower()):
        return word.lower()
    return word    
word = input().strip()
print(c(word))