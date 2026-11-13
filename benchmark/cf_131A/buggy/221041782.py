s = input()
if s[0] >= 'a' and s[1] < 'a':
    print(s[0].upper(), end='')
    for i in range(1, len(s)):
        print(s[i].lower(), end='')
elif s[0] < 'a' and s[1] < 'a':
    print(s.lower())
else:
    print(s)