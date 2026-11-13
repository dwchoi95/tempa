word = input()
def correct(x):
    if len(x) == 1:
        correct_word = x.upper()
    else:
        correct_word = x[0].upper() + x[1:].lower()
    return correct_word
print(correct(word))