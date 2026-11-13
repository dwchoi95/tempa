def cAPS_lOCK(string):
    if string[1:].isupper():
        return string.capitalize()
    elif string.isupper():
        return string.capitalize()
    else :
        return string

if __name__ == "__main__" :
    string = input()
    print(cAPS_lOCK(string))