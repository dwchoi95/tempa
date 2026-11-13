strInput = list(input())                                 
                                                         
for i in range(len(strInput)):                           
    if i > 0 and strInput[i].isupper():                  
        for x in range(len(strInput)):                   
            if strInput[x].isupper():                    
                strInput[x] = strInput[x].lower()        
            else:                                        
                strInput[x] = strInput[x].upper()        
        break                                            
                                                         
print(''.join(strInput))