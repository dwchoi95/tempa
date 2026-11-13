strInput = list(input())                       
                                               
for i in range(len(strInput)):                 
    if i > 0 and strInput[i].isupper():        
        strInput[i] = strInput[i].lower()      
        strInput[0] = strInput[0].upper()      
                                               
print(''.join(strInput))