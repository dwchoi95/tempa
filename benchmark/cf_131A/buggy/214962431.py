word = input()

def shouldGetFix(word):
    for i in range (1,len(word)):
        if word[i].islower():
            return False
    return True

def allUpper(word):
    for i in range (len(word)):
        if word[i].islower():
            return False
    return True

def shouldGetFix(word):
    for i in range (1,len(word)):
        if word[i].islower():
            return False
    return True

if len(word) == 1:
    print(word.upper())
elif allUpper(word):
    print(word.lower())
elif shouldGetFix(word):
    print(word.lower().capitalize())
else:
    print(word)