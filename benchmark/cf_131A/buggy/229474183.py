word = input() 

if word.isupper(): 
    print(word.lower()) 
elif word[1:].isupper(): 
    print(word[0] + word[1:].lower()) 
else:
    print(word)