word = input()
sol = ''
if word[1:].isupper():
    for x in word:
        if x.isupper():
            sol += x.lower()
        else:
            sol += x.upper()
elif word.islower():
    sol = word.upper()
else:
    sol = word
print(sol)