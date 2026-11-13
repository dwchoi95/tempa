word = input()

newWord = ""

newWord += word[0].upper()
newWord += word[1:].lower()

print(newWord)