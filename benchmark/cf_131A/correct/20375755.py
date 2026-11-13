def isCapsLock(string):

    for i in range(1, len(string)):

        if(string[i].islower()):

            return False

    return True

    

def toggleCase(string):

    x = list(string)

    for i in range(len(x)):

        if(x[i].isupper()):

            x[i] = x[i].lower()

        else:

            x[i] = x[i].upper()

    return ''.join(x)



string = input()

if(isCapsLock(string)):

    string = toggleCase(string)

print(string)