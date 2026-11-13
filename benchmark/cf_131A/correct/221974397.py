def cAPS_lOCK(word):
    if word.isupper() or (word[0].islower() and all(ch.isupper() for ch in word[1:])):
        return word.swapcase()
    else :
        return word

if __name__ == "__main__":
    word = input()
    print(cAPS_lOCK(word))