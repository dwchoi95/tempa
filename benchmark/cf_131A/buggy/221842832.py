inputWord = input()
if inputWord.isupper() or (inputWord[0].islower() and inputWord[1:].isupper()):
    print(inputWord.capitalize)
else:
    print(inputWord)