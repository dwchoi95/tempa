#counter_capital=0
#counter_small=0
word=input()
lol=len(word)
if len(word)==1:
    if word.islower():
        print(word.upper())
    else:
        print(word.lower())
elif word[1::].isupper() or word.isupper():
    print(word.swapcase())
else:
    print(word)