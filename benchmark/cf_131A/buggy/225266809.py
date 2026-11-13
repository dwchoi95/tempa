def caps():
    word = str(input())
    if word.upper() == word:
        return word.title()
    elif word.upper()[1:] == word[1:]:
        return word.title()
    else:
        return word
print(caps())