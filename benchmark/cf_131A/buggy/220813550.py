word = input()
n = len(word)
sm = 0
if(ord('A') <= ord(word[0]) <= ord('Z')):
    for c in word:
        if(ord('a') <= ord(c) <= ord('z')):
            sm+=1
            break
    if sm == 1:
        # Make small
        for i in range(n):
            if i == 0:
                print(word[i], end='')
            elif(ord('a') <= ord(word[i]) <= ord('z')):
                print(word[i], end='')
            else:
                print(chr(97+ord(word[i])-ord('A')), end='')
    else:
        for i in range(n):
            if i == 0:
                print(word[i], end='')
            elif(ord('a') <= ord(word[i]) <= ord('z')):
                print(chr(ord('A')+ord(word[i])-ord('a')), end='')
            else:
                print(word[i], end='')
else:
    for i in range(n):
        if(i == 0):
            if(ord('a') <= ord(word[i]) <= ord('z')):
                print(chr(ord('A')+ord(word[i])-ord('a')), end='')
            else:
                print(word[i], end='')
        elif(ord('a') <= ord(word[i]) <= ord('z')):
            print(word[i], end='')
        else:
            print(chr(97+ord(word[i])-ord('A')), end='')
print()