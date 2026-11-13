word = input()

if word == word.capitalize() or word[0:] == word[0:].capitalize() or len(word) == 1:
    fin = ""
    for i in word:
        if i == i.lower():
            fin += i.capitalize()
        else:
            fin += i.lower()
    print(fin)