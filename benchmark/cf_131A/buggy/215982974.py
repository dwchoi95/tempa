def apply_caps_lock_rule(word):
    if word.isupper() or word[1:].isupper():
        return word.swapcase()
    return word
word = input()
print(apply_caps_lock_rule(word))