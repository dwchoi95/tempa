s = input()
if (len(s) == 1 and s[0].lower() == s[0]):
    print(s[0].upper())

else:
    c = s[0]
    cur = ''
    for i in range(1, len(s)):
        cur += s[i]
    if (cur == cur.lower() and c == c.lower()):
        ans = c + cur
        print(ans)
    else:
        ans = c.upper() + cur.lower()
        print(ans)

# Wed Nov 01 2023 22:55:41 GMT+0300 (Moscow Standard Time)