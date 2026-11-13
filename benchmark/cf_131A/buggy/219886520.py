s = input()

txt = ''
for char in s:
    if char.isupper():
        txt += char.lower()
    else:
        txt += char.upper()

print(txt)