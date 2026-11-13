word = input()

if word[0].islower():
    word = word[0].upper() + word[1:]
print(word)