import re

word = input()
ans = re.findall(r'^[a-z]?[A-Z]+', word)
if ans[0] == word:
    print(word.capitalize())
else:
    print(word)