word = input()  # No need to use str() for input

copy = word
n = len(word)
is_valid = True

# Check and modify the first character if it's a lowercase letter
if 'a' <= copy[0] <= 'z':
    copy = copy[0].upper() + copy[1:]

# Loop through the rest of the characters
for i in range(1, n):
    if 'A' <= copy[i] <= 'Z':
        copy = copy[:i] + copy[i].lower() + copy[i+1:]
    else:
        is_valid = False
        break

if is_valid:
    print(copy)
else:
    print(word)