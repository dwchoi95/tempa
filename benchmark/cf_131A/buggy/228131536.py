import re

word = input()
if re.search(r'^[a-z][A-Z]$', word):
    print(word.swapcase())

else:
    if re.search(r'^[A-Z]$', word):
        print(word.swapcase())
    else:
        print(word)