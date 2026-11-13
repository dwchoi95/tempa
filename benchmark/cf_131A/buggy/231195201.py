word = input()
word = list(word)

for i in range(len(word)):
    word[i] = word[i].lower()
if word[0] in "abcdefghijklmnopqrstuvwxyz":
    word[0] = word[0].upper()
print("".join(word))