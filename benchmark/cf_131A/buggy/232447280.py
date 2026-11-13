word = input()
hi = word[0].upper()
poop = word.replace(word[0], '', 1).lower()
print(hi + poop)