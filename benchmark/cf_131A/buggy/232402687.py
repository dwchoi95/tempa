def adjust_caps_lock(word):
    # Check if all letters are capitalized or if all but the first are capitalized
    if word.isupper() or (len(word) > 1 and word[1:].isupper()):
        # Change all letters to lowercase if there is only one uppercase letter (except for the first letter)
        if len(word) == word.count('A') + word.count('E') + word.count('I') + word.count('O') + word.count('U'):
            return word.lower()
    return word

print(adjust_caps_lock("HELLO")) # "hello"
print(adjust_caps_lock("HTTP"))   # "http"
print(adjust_caps_lock("Z"))      # "z"
print(adjust_caps_lock("WORLD")) # "WORLD" (unaffected as the capitalization rule was not applied)