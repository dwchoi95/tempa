inputWord = input()
if len(inputWord)==1:
    print(inputWord.capitalize())
elif inputWord[0].islower() and inputWord[1:].isupper:
    print(inputWord.capitalize())