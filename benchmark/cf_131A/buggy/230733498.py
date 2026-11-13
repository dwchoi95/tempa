n = input()
s = ''

for i in n:
    if i.isupper():
        s += i.lower()
    else:
        s += i.upper()

s = s[0].upper() + s[1:]

print(s)