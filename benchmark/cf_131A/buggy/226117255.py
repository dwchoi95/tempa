import re

word = input()
ans = re.findall(r'^[A-Z][a-z]+', word)
if ans:
    print(word)
else:
    print(word.swapcase())