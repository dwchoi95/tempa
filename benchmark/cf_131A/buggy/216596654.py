def check_case(s):
    x = s[1:]
    y = s[0]
    if s.isupper() or (y.islower() and x.isupper()):
        return True
    else:
        return False


def reverse_case(s):
    string_list = list(s)
    for i in range(len(string_list)):
        if string_list[i].isupper():
            string_list[i] = string_list[i].lower()
        else:
            string_list[i] = string_list[i].upper()

    new_string = ""
    for char in string_list:
        new_string += char
    return new_string


s = input()
if check_case(s):
    print(reverse_case(s))
else:
    print(s)