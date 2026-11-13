word = input().strip()
if word.isupper() or (word[1:].isupper() and word[0].islower()):
   c = word.lower()  
else:
    c = word
print(c)