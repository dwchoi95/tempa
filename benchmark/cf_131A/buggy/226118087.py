import re

word = input()
# ans = re.findall(r'^[A-Z]+[a-z]+', word)
if re.findall(r'^[a-z][A-Z]+', word) or re.findall(r'^[A-Z]+', word):
    print(word.swapcase())

else:
    print(word)