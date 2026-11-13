t = input()
for i in range(1, len(t)):
    if ord(t[i]) > 97:
        m = 1
        break
    else:
        m = 0
if m == 0:
    print(t.title())
else:
    print(t)