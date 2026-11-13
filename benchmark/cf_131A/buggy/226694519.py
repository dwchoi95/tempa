word = input()
def meets_caps_lock_rule(word):
    return word.isupper() or (word[0].islower() and word[1:].isupper())
if meets_caps_lock_rule(word):
    result = word.swapcase()
else:
    result = word
print(result)