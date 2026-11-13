def change_case(word):
    if word.isupper():
        return word.lower()
    elif word.istitle():
        return word.swapcase()
    else:
        return word

def correct_capitalization(sentence):
    words = sentence.split()
    corrected_words = [change_case(word) for word in words]
    return ' '.join(corrected_words)

sentence = "H e L L O HTTP z"
corrected_sentence = correct_capitalization(sentence)
print(corrected_sentence)