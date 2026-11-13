word = input()

if word.isupper() == True or word[0].islower() == True and word[1:].isupper() == True:
    string = ""
    letters = []
    for x in word:
        letters.append(x)
    for x in letters:
        if x.isupper():
            x = str(x).lower()
        else:
            x = str(x).upper()
        string += x
    print(string)
else:
    print(word)