string = input()

answer = ''
if len(string) == 1 or string[1:].isupper():
    for char in string:
        answer += (char.upper() if char.islower() else char.lower())
else:
    answer = string
print(answer)