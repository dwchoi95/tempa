s = input()

if len(s) >= 2:
    result = s.lower() if s.isupper() else s[0].upper() + s[1:].lower() \
                if s[0].islower() and s[1:].isupper() else s
else:
    result = s.lower() if s.isupper() else s.upper()

print(result)