n =input()
string_year = ""
for i in range(len(n)):
    substring = n[1:]
    if n[0].islower() and substring.islower():
        string_year = n[0].upper() + substring.lower()
    elif n[0].isupper() and substring.isupper():
        string_year = n[0].lower() + substring.lower()
    elif n[0].islower and substring.isupper():
        string_year = n[0].upper() + substring.lower()
    else :
        string_year = n
print(string_year)