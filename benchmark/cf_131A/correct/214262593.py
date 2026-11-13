word = input()

if word == word.upper() or word[1:] == word[1:].upper() or len(word) == 1:
    fin = ""
    for i in word:
        if i == i.lower():
            fin += i.upper()
        else:
            fin += i.lower()

    print(fin)
else:

    print(word)