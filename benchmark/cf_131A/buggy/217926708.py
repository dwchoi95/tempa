word =str(input())
word2=""
if word.islower():
    print(word)
elif word.isupper():
    print(word)
else:
    for let in word:
        
        if let.islower():
            let=let.upper()
            word2+=let
            
        elif let.isupper():
            let=let.lower()
            word2+=let
            
print(word2)