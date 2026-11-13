def create_list(word):
    list0 = []
    for letter in word:
        list0.append(letter)
    return list0

def check_caps(word):
    if word[0].isupper() and word[1].islower(): # Lock
        return 0
    elif word[0].islower: # lOCK
        return 1
    elif word[0].isupper() and word[1].isupper(): # LOCK
        return 2

def assemble_list(l):
    word = "".join(l)
    return word

def caps(word):
    l = create_list(word)
    if check_caps(word) == 1:
        for i in range(0, len(l)):
            if l[i].islower():
                l[i] = l[i].upper()
            else:
                l[i] = l[i].lower()
    elif check_caps(word) == 2:
        for i in range(0, len(l)):
            if l[i].isupper():
                l[i] = l[i].lower()
    word = assemble_list(l)
    return word

if __name__ == '__main__':
    word = input().strip()
    print(caps(word))