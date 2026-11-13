word = input()
def check(word):
    if word[0].islower() and word[1:].isupper():
        return True
    else:
        return False

if word.isupper() or check(word) or len(word) == 1:
    print(word.swapcase())
else:
    print(word)