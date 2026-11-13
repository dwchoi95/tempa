word = input()
sm = 0
for c in word:
    if(c.islower()):
        sm += 1
        break
print(word[0].upper(), end='')
if(sm == 1):
    print(word[1:].lower(), end='')
else:
    print(word[1:].upper(), end='')
print()