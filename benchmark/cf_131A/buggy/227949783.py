s = input()
ans = []
l = "qwertyuiopasdfghjklzxcvbnm"
b = "QWERTYUIOPASDFGHJKLZXCVBNM"
z = 0
for i in range(1, len(s)):
    if s[i] in l:
        z += 1
        break
if s[0] in l:
    ans.append(b[l.index(s[0])])
else:
    ans.append(s[0])
for i in range(1, len(s)):
    if s[i] in b:
        ans.append(l[b.index(s[i])])
    else:
        ans.append(s[i])

ans = "".join(ans)
if z == 0:
    print(ans)
else:
    print(s)