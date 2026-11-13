s=str(input())
def qns(word):
    if word.isupper() or word[1:].isupper() or len(word)==1:
        return word.swapcase()
    else:
        return word
print(qns(s))