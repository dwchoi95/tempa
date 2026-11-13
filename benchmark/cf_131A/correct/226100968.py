word = input()
if len(word) ==1 and word[0].islower() :
    print(word.upper())
elif len(word) ==1 and word[0].isupper() :
    print(word.lower())    
elif word.isupper() or word[0].islower() and word[1:].isupper() :
    print(word.swapcase())
else :
    print(word)