from collections import Counter
import math
import re
s = input()
f, cnt = -1, 0
for i in range(len(s)):
    if s[i] >= 'A' and s[i] <= 'Z':
        if f == -1: f = i
        cnt += 1

if cnt == len(s) or cnt == len(s) - 1 and f == 1:
    ans = ''
    for i in range(len(s)):
        if s[i] >= 'A' and s[i] <= 'Z':
            ans += chr(97 + ord(s[i]) - 65)
        else:
            ans += chr(65 + ord(s[i]) - 97)
    print(ans)
else:
    print(s)