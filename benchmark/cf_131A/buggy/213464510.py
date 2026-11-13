word = input()
def correct(x):
    correct_word = x
    if len(x) == 1:
        correct_word = x.upper()
    elif len(x) > 1 and x[0] == x[0].lower() and x[1:] == x[1:].upper():
        correct_word = x[0].upper() + x[1:].lower()
    elif len(x) > 1 and x == x.upper():
        correct_word = x[0].upper() + x[1:].lower()
    return correct_word
print(correct(word))