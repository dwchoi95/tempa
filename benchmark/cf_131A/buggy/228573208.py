word = input()
ok = 1
for i in range(1, len(word)):
    if word[i] >= 'a' and word[i] <= 'z':
        ok = 0
if ok == 1:
    print(word[0].upper(),end='')
    print(word[1:].lower())
else:
    print(word)