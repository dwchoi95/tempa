words = input()

if words.isupper() or words[1:].isupper():
    pro_words = words.swapcase()
else:
    pro_words = words  


print(pro_words)