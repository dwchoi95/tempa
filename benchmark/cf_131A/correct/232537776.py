alphabets = [chr(i) for i in range(ord('a'), ord('z')+1)]
new_word = str(input())
word = ""
ln = len(new_word)
if 90 < ord(new_word[0]) <= 122:
    count = 0
    p = 1
    while p < ln:
        i = 0
        while i < 26:
            if new_word[p] == alphabets[i]:
                count += 1
            i += 1
        p += 1
    if count > 0:
        word = new_word
    if count == 0:
        word += new_word[0].capitalize()
        word += new_word[1:ln].lower()
if 65 <= ord(new_word[0]) <= 90:
    count = 0
    p = 1
    while p < ln:
        i = 0
        while i < 26:
            if new_word[p] == alphabets[i]:
                count += 1
            i += 1
        p += 1
    if count == 0:
        word = new_word.lower()
    if count > 0:
        word = new_word
print(word)