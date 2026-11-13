word = input()

def shouldGetFix(word):
    for i in range (1,len(word)):
        print(word[i])
        if word[i].islower():
            return False
    return True

if len(word) == 1:
    print(word.upper())
elif shouldGetFix(word):
    print(word.lower().capitalize())
else:
    print(word)