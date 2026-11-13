def cAPS_lOCK(string):
    if len(string) == 1 :
        return string.capitalize()
    if string[0] == string[1]:
        return string.lower()
    elif string[1:].isupper():
        return string.capitalize()
    elif string.isupper():
        return string.capitalize()
    else :
        return string

if __name__ == "__main__" :
    string = input()
    print(cAPS_lOCK(string))