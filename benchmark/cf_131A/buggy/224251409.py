s = input()
ans = s[0].upper() + s[1:].lower()

for i in range(1, len(s)):
    if ord('a') <= ord(s[i]) <= ord('z') and \
            ord('a') <= ord(s[1]) <= ord('z') or \
            ord('A') <= ord(s[i]) <= ord('Z') and \
            ord('A') <= ord(s[1]) <= ord('Z'):
        continue
    ans = s
    break

print(ans)