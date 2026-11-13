def process_word(word):
    
    if word.isupper() or word[1:].islower():
        return word.swapcase()  
    else:
        return word  


input_word = input()


result = process_word(input_word)
print(result)