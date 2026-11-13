def check(s, n):
    for i in range(n, len(s)):
        if (s[i].islower()):
            return 0
    return 1

s = input()
if check(s, 0):
    res = s.lower()
elif check(s, 1):
    res = s[0].upper() + s[1:].lower()
else:
    res = s
print(res)