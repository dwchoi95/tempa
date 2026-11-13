s = input()
for i in range(len(s)):
    if i != 0 and s[i].islower():
        print(s)
        exit()

print(s[0].upper() + s[1:].lower() if s[0].islower() else s.lower())