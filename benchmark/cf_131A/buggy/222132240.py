x = input()  # Take user input as a string
string = ''

# Check if all characters are lowercase
if x.islower():
    string = x.lower()  # Convert the entire string to lowercase
else:
    # Check if the first character is uppercase and all others are lowercase
    if x[0].isupper() and x[1:].islower():
        string = x.capitalize()  # Capitalize the first character and convert the rest to lowercase
    else:
        string = x  # No changes needed, keep the string as it is

print(string)