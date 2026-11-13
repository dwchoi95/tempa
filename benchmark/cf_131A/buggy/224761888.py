line = input()
if line[1:]==line[1:].upper():
    print(line[0].upper()+line[1:].lower())
else:
    print(line)