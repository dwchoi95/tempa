test = input()

def makeCaps(word):
    newWord = "Test"
    if word.isupper():
        newWord = word.lower()
    elif word[0].islower() and word[1:].isupper():
         newWord = word[0].upper()       
         newWord += word[1:].lower()   
    else:
         newWord =  word
    return newWord        
 

print(makeCaps(test))