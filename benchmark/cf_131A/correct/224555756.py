s = input()
S = []
for i in range(len(s)):
    S.append(s[i])
x = 0
if s[0] == s[0].upper():
    for i in range(1,len(s)):
        if s[i] == s[i].upper():
            pass
        else:
            x = 1
else:
    for i in range(1,len(s)):
        if s[i] == s[i].upper():
            pass
        else:
            x = 1
if x == 1:
    print(s)
else:
    for i in range(len(s)):
        if S[i] == S[i].upper():
            S[i] = S[i].lower()
        else:
            S[i] = S[i].upper()
    s1 = ''
    for letter1 in S:
        s1 += letter1
    print(s1)