n = input()
modified_string = ""

are_all_uppercase = all(char.isupper() for char in n)
except_first_letter = all(char.isupper() for char in n[1:])

if are_all_uppercase or except_first_letter:
    for i in n:
        if i.isupper():
            modified_string += i.lower()
        else:
            modified_string += i.upper()
    
    print(modified_string)
else:
    print(n)