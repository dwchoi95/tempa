string = input()
check = True
for i in range(1, len(string)):
    if string[i].islower():
        check = False
        break

if check:
    for s in string:
        if s.islower():
            print(s.upper(), end="")
        else:
            print(s.lower(), end="")
    print("")
else:
    print(string)