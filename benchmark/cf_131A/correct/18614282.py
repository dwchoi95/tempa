word = input()

c = s = 0

l = len(word)

for w in word:

    if w >= 'a' and w <= 'z':

        s += 1

    elif w >= 'A' and w <= 'Z':

        c += 1



if c == l:

    print(word.lower())

elif (word[0] >= 'a' and word[0] <= 'z') and c == l-1:

    print(word.title())

else:

    print(word)