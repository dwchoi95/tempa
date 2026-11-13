s = input()
for i in range(len(s)):
    if i != 0 and s[i].islower():
        print(s)
        exit()

print(s.lower())