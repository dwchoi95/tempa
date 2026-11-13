import re

word = input()
ans = re.findall(r'^[A-Z][a-z]+', word)
if ans or re.findall(r'^[a-z]+[A-Z]+[a-z]', word):
    print(word)

else:
    print(word.swapcase())