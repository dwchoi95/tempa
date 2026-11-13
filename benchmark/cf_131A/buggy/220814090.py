word = input()
sm = 0
for c in word:
    if(c.islower()):
        sm += 1
        break
if(sm == 1):
    print(word[0].lower(), end='')
    print(word[1:].upper(), end='')
else:
    print(word, end='')
print()