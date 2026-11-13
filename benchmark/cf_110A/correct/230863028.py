s = input()
cn = 0
ln = len(s)

for i in range(ln):
    if s[i] == '4' or s[i] == '7':
        cn += 1

if cn == 4 or cn == 7:
    print("YES")
else:
    print("NO")