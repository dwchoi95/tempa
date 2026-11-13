n = input()

s = ''

for i in n:
    s+=i.lower() if i.isupper() else i.upper()

print(s)